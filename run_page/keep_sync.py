import argparse
import base64
import json
import os
import time
import zlib
from collections import namedtuple
from datetime import datetime, timedelta, timezone
from xml.dom import minidom
import eviltransform
import gpxpy
import polyline
import requests
from config import (
    GPX_FOLDER,
    JSON_FILE,
    SQL_FILE,
    TCX_FOLDER,
    run_map,
    start_point,
)
from Crypto.Cipher import AES
from generator import Generator
from utils import adjust_time
import xml.etree.ElementTree as ET

KEEP_SPORT_TYPES = ["running", "hiking", "cycling"]
KEEP2STRAVA = {
    "outdoorWalking": "Walk",
    "outdoorRunning": "Run",
    "outdoorCycling": "Ride",
    "indoorRunning": "VirtualRun",
    "mountaineering": "Hiking",
}
KEEP2TCX = {
    "outdoorWalking": "Walking",
    "outdoorRunning": "Running",
    "outdoorCycling": "Biking",
    "indoorRunning": "Running",
    "mountaineering": "Hiking",
}

# need to test
LOGIN_API = "https://api.gotokeep.com/v1.1/users/login"
RUN_DATA_API = "https://api.gotokeep.com/pd/v3/stats/detail?dateUnit=all&type={sport_type}&lastDate={last_date}"
RUN_LOG_API = "https://api.gotokeep.com/pd/v3/{sport_type}log/{run_id}"

HR_FRAME_THRESHOLD_IN_DECISECOND = 100  # Maximum time difference to consider a data point as the nearest, the unit is decisecond(分秒)

TIMESTAMP_THRESHOLD_IN_DECISECOND = 3_600_000  # Threshold for target timestamp adjustment, the unit of timestamp is decisecond(分秒), so the 3_600_000 stands for 100 hours sports time. 100h = 100 * 60 * 60 * 10

# If your points need trans from gcj02 to wgs84 coordinate which use by Mapbox
TRANS_GCJ02_TO_WGS84 = True

# Keep's stats API sometimes reports one real-world run as several separate
# logs (e.g. each auto-pause/resume segment becomes its own log while Keep's
# own app still shows it as a single workout). Consecutive logs of the same
# sport type whose gap is within this many seconds are merged back into one
# activity. Set KEEP_MERGE_GAP_THRESHOLD_IN_SECONDS=0 to disable merging.
KEEP_MERGE_GAP_THRESHOLD_IN_SECONDS = int(
    os.getenv("KEEP_MERGE_GAP_THRESHOLD_IN_SECONDS", 30 * 60)
)

# Only the "representative" (earliest) segment id of a merged group ends up
# stored as an activity id in the database, so the other segment ids would
# look "new" again on every future sync and get merged into a second,
# duplicate activity. This file remembers every segment id that has already
# been folded into some activity so it can be skipped on later syncs.
KEEP_MERGED_SEGMENT_IDS_FILE = os.path.join(
    os.path.dirname(SQL_FILE), "keep_merged_segment_ids.json"
)


def _load_consumed_segment_ids():
    if not os.path.exists(KEEP_MERGED_SEGMENT_IDS_FILE):
        return set()
    try:
        with open(KEEP_MERGED_SEGMENT_IDS_FILE) as f:
            return set(json.load(f))
    except Exception as e:
        print(f"Something wrong reading {KEEP_MERGED_SEGMENT_IDS_FILE}: {e}")
        return set()


def _save_consumed_segment_ids(ids):
    with open(KEEP_MERGED_SEGMENT_IDS_FILE, "w") as f:
        json.dump(sorted(ids), f)


def login(session, mobile, password):
    headers = {
        "User-Agent": "Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:78.0) Gecko/20100101 Firefox/78.0",
        "Content-Type": "application/x-www-form-urlencoded;charset=utf-8",
    }
    data = {"mobile": mobile, "password": password}
    r = session.post(LOGIN_API, headers=headers, data=data)
    if r.ok:
        token = r.json()["data"]["token"]
        headers["Authorization"] = f"Bearer {token}"
        return session, headers


def get_to_download_runs_ids(session, headers, sport_type):
    last_date = 0
    result = []

    while 1:
        r = session.get(
            RUN_DATA_API.format(sport_type=sport_type, last_date=last_date),
            headers=headers,
        )
        if r.ok:
            run_logs = r.json()["data"]["records"]

            for i in run_logs:
                logs = [j["stats"] for j in i["logs"]]
                result.extend(k["id"] for k in logs if not k["isDoubtful"])
            last_date = r.json()["data"]["lastTimestamp"]
            since_time = datetime.fromtimestamp(last_date // 1000, tz=timezone.utc)
            print(f"pares keep ids data since {since_time}")
            time.sleep(1)  # spider rule
            if not last_date:
                break
    return result


def get_single_run_data(session, headers, run_id, sport_type):
    r = session.get(
        RUN_LOG_API.format(sport_type=sport_type, run_id=run_id), headers=headers
    )
    if r.ok:
        return r.json()


def decode_runmap_data(text, is_geo=False):
    _bytes = base64.b64decode(text)
    key = "NTZmZTU5OzgyZzpkODczYw=="
    iv = "MjM0Njg5MjQzMjkyMDMwMA=="
    if is_geo:
        cipher = AES.new(base64.b64decode(key), AES.MODE_CBC, base64.b64decode(iv))
        _bytes = cipher.decrypt(_bytes)
    run_points_data = zlib.decompress(_bytes, 16 + zlib.MAX_WBITS)
    run_points_data = json.loads(run_points_data)
    return run_points_data


def _decode_and_process_points(run_data):
    """Decode geoPoints/heartRate for a single Keep log.

    Returns (points, avg_heart_rate). Each point has its coordinates
    transformed to WGS84 and the nearest heart rate sample attached (if
    any). Its "timestamp" is normalized to an absolute decisecond unix
    timestamp (rather than a delta from this log's own start time) so
    points from multiple logs can be concatenated when merging segments
    that belong to the same real-world run (see
    KEEP_MERGE_GAP_THRESHOLD_IN_SECONDS).
    """
    start_time = run_data["startTime"]
    avg_heart_rate = None
    decoded_hr_data = []
    if run_data["heartRate"]:
        avg_heart_rate = run_data["heartRate"].get("averageHeartRate", None)
        heart_rate_data = run_data["heartRate"].get("heartRates", None)
        if heart_rate_data:
            decoded_hr_data = decode_runmap_data(heart_rate_data)
        # fix #66
        if avg_heart_rate and avg_heart_rate < 0:
            avg_heart_rate = None

    points = []
    if run_data["geoPoints"]:
        run_points_data = decode_runmap_data(run_data["geoPoints"], True)
        if TRANS_GCJ02_TO_WGS84:
            wgs84_points = [
                list(eviltransform.gcj2wgs(p["latitude"], p["longitude"]))
                for p in run_points_data
            ]
            for i, p in enumerate(run_points_data):
                p["latitude"] = wgs84_points[i][0]
                p["longitude"] = wgs84_points[i][1]

        for p in run_points_data:
            if "timestamp" not in p:
                if "unixTimestamp" in p:
                    p["timestamp"] = p["unixTimestamp"]
                else:
                    p["timestamp"] = 0
            p_hr = find_nearest_hr(decoded_hr_data, int(p["timestamp"]), start_time)
            if p_hr:
                p["hr"] = p_hr
            if p["timestamp"] <= TIMESTAMP_THRESHOLD_IN_DECISECOND:
                p["timestamp"] = start_time // 100 + p["timestamp"]
        points = run_points_data
    return points, avg_heart_rate


def build_activity_from_group(group, old_gpx_ids, old_tcx_ids, with_gpx=False, with_tcx=False):
    """Build a single activity namedtuple from one or more Keep logs.

    ``group`` is a list of raw Keep run_data dicts (as returned by
    get_single_run_data) that are believed to be segments of the same
    real-world run (see KEEP_MERGE_GAP_THRESHOLD_IN_SECONDS) and should be
    combined into one activity.
    """
    segs = sorted((g["data"] for g in group), key=lambda s: s["startTime"])
    data_type = segs[0]["dataType"]
    # 5898009e387e28303988f3b7_9223370441312156007_rn middle
    keep_id = segs[0]["id"].split("_")[1]

    all_points = []
    hr_weighted_sum = 0.0
    hr_weighted_duration = 0
    for seg in segs:
        points, avg_hr = _decode_and_process_points(seg)
        all_points.extend(points)
        if avg_hr and seg.get("duration"):
            hr_weighted_sum += avg_hr * seg["duration"]
            hr_weighted_duration += seg["duration"]
    avg_heart_rate = (
        hr_weighted_sum / hr_weighted_duration if hr_weighted_duration else None
    )

    start_time = segs[0]["startTime"]
    end_time = max(seg["endTime"] for seg in segs)
    duration = sum(seg["duration"] for seg in segs if seg.get("duration"))
    distance = sum(seg.get("distance", 0) for seg in segs)

    elevation_gain = None
    if all_points:
        if data_type.startswith("outdoor") or data_type == "mountaineering":
            if with_gpx:
                gpx_data = parse_points_to_gpx(
                    all_points, start_time, KEEP2STRAVA[data_type]
                )
                elevation_gain = gpx_data.get_uphill_downhill().uphill
                if str(keep_id) not in old_gpx_ids:
                    download_keep_gpx(gpx_data.to_xml(), str(keep_id))
            if with_tcx:
                tcx_run_data = {
                    "startTime": start_time,
                    "duration": duration,
                    "distance": distance,
                    "calorie": sum(seg.get("calorie", 0) or 0 for seg in segs)
                    or None,
                }
                tcx_data = parse_points_to_tcx(
                    tcx_run_data, all_points, KEEP2TCX[data_type]
                )
                if str(keep_id) not in old_tcx_ids:
                    download_keep_tcx(tcx_data.toprettyxml(), str(keep_id))
    else:
        print(f"ID {keep_id} no gps data")

    coords = [[p["latitude"], p["longitude"]] for p in all_points]
    polyline_str = polyline.encode(coords) if coords else ""
    start_latlng = start_point(*coords[0]) if coords else None
    start_date = datetime.fromtimestamp(start_time // 1000, tz=timezone.utc)
    tz_name = segs[0].get("timezone", "")
    start_date_local = adjust_time(start_date, tz_name)
    end = datetime.fromtimestamp(end_time // 1000, tz=timezone.utc)
    end_local = adjust_time(end, tz_name)
    if not duration:
        print(f"ID {keep_id} has no total time just ignore please check")
        return
    d = {
        "id": int(keep_id),
        "name": f"{KEEP2STRAVA[data_type]} from keep",
        # future to support others workout now only for run
        "type": f"{KEEP2STRAVA[data_type]}",
        "subtype": f"{KEEP2STRAVA[data_type]}",
        "start_date": datetime.strftime(start_date, "%Y-%m-%d %H:%M:%S"),
        "end": datetime.strftime(end, "%Y-%m-%d %H:%M:%S"),
        "start_date_local": datetime.strftime(start_date_local, "%Y-%m-%d %H:%M:%S"),
        "end_local": datetime.strftime(end_local, "%Y-%m-%d %H:%M:%S"),
        "length": distance,
        "average_heartrate": int(avg_heart_rate) if avg_heart_rate else None,
        "map": run_map(polyline_str),
        "start_latlng": start_latlng,
        "distance": distance,
        "moving_time": timedelta(seconds=duration),
        "elapsed_time": timedelta(seconds=int((end_time - start_time) // 1000)),
        "average_speed": distance / duration,
        "elevation_gain": elevation_gain,
        "location_country": str(segs[0].get("region", "")),
    }
    return namedtuple("x", d.keys())(*d.values())


def group_runs_to_merge(sorted_raw_runs):
    """Cluster consecutive same-sport-type Keep logs that are close enough
    in time to be segments of the same real-world run (see
    KEEP_MERGE_GAP_THRESHOLD_IN_SECONDS) instead of separate activities.

    ``sorted_raw_runs`` must already be sorted by startTime.
    """
    if not sorted_raw_runs:
        return []
    threshold_ms = KEEP_MERGE_GAP_THRESHOLD_IN_SECONDS * 1000
    groups = [[sorted_raw_runs[0]]]
    for run_data in sorted_raw_runs[1:]:
        prev_seg = groups[-1][-1]["data"]
        seg = run_data["data"]
        gap_ms = seg["startTime"] - prev_seg["endTime"]
        if (
            threshold_ms
            and 0 <= gap_ms <= threshold_ms
            and seg["dataType"] == prev_seg["dataType"]
        ):
            groups[-1].append(run_data)
        else:
            groups.append([run_data])
    return groups


def get_all_keep_tracks(
    email,
    password,
    old_tracks_ids,
    keep_sports_data_api,
    with_gpx=False,
    with_tcx=False,
):
    if with_gpx and not os.path.exists(GPX_FOLDER):
        os.mkdir(GPX_FOLDER)
    if with_tcx and not os.path.exists(TCX_FOLDER):
        os.mkdir(TCX_FOLDER)
    s = requests.Session()
    s, headers = login(s, email, password)
    tracks = []
    consumed_segment_ids = _load_consumed_segment_ids()
    newly_consumed_segment_ids = set()
    for api in keep_sports_data_api:
        runs = get_to_download_runs_ids(s, headers, api)
        runs = [
            run
            for run in runs
            if run.split("_")[1] not in old_tracks_ids
            and run.split("_")[1] not in consumed_segment_ids
        ]
        print(f"{len(runs)} new keep {api} data to generate")
        old_gpx_ids = []
        if with_gpx:
            old_gpx_ids = os.listdir(GPX_FOLDER)
            old_gpx_ids = [
                i.split(".")[0] for i in old_gpx_ids if not i.startswith(".")
            ]
        old_tcx_ids = []
        if with_tcx:
            old_tcx_ids = os.listdir(TCX_FOLDER)
            old_tcx_ids = [
                i.split(".")[0] for i in old_tcx_ids if not i.startswith(".")
            ]
        raw_runs = []
        for run in runs:
            print(f"downloading keep id {run}")
            try:
                run_data = get_single_run_data(s, headers, run, api)
                if run_data and run_data.get("data"):
                    raw_runs.append(run_data)
            except Exception as e:
                print(f"Something wrong downloading keep id {run}: " + str(e))
        raw_runs.sort(key=lambda r: r["data"]["startTime"])

        for group in group_runs_to_merge(raw_runs):
            ids = [g["data"]["id"] for g in group]
            print(f"parsing keep id(s) {ids}")
            try:
                track = build_activity_from_group(
                    group, old_gpx_ids, old_tcx_ids, with_gpx, with_tcx
                )
                if track is not None:
                    tracks.append(track)
                    newly_consumed_segment_ids.update(
                        i.split("_")[1] for i in ids
                    )
            except Exception as e:
                print(f"Something wrong paring keep id(s) {ids}: " + str(e))

    if newly_consumed_segment_ids:
        _save_consumed_segment_ids(consumed_segment_ids | newly_consumed_segment_ids)
    return tracks


def parse_points_to_gpx(run_points_data, start_time, sport_type):
    """
    Convert run points data to GPX format.

    Args:
        run_id (str): The ID of the run.
        run_points_data (list of dict): A list of run data points.
        start_time (int): The start time for adjusting timestamps. Note that the unit of the start_time is millisecond

    Returns:
        gpx_data (str): GPX data in string format.
    """
    points_dict_list = []
    # early timestamp fields in keep's data stands for delta time, but in newly data timestamp field stands for exactly time,
    # so it doesn't need to plus extra start_time
    if (
        run_points_data
        and run_points_data[0]["timestamp"] > TIMESTAMP_THRESHOLD_IN_DECISECOND
    ):
        start_time = 0

    for point in run_points_data:
        points_dict = {
            "latitude": point["latitude"],
            "longitude": point["longitude"],
            # note that the timestamp of a point is decisecond(分秒)
            "time": datetime.fromtimestamp(
                (start_time // 1000 + point["timestamp"] // 10),
                tz=timezone.utc,
            ),
            "elevation": point.get("altitude"),
            "hr": point.get("hr"),
        }
        points_dict_list.append(points_dict)
    gpx = gpxpy.gpx.GPX()
    gpx.nsmap["gpxtpx"] = "http://www.garmin.com/xmlschemas/TrackPointExtension/v1"
    gpx_track = gpxpy.gpx.GPXTrack()
    gpx_track.name = "gpx from keep"
    gpx_track.type = sport_type
    gpx.tracks.append(gpx_track)

    # Create first segment in our GPX track:
    gpx_segment = gpxpy.gpx.GPXTrackSegment()
    gpx_track.segments.append(gpx_segment)
    for p in points_dict_list:
        point = gpxpy.gpx.GPXTrackPoint(
            latitude=p["latitude"],
            longitude=p["longitude"],
            time=p["time"],
            elevation=p.get("elevation"),
        )
        if p.get("hr") is not None:
            gpx_extension_hr = ET.fromstring(
                f"""<gpxtpx:TrackPointExtension xmlns:gpxtpx="http://www.garmin.com/xmlschemas/TrackPointExtension/v1">
                    <gpxtpx:hr>{p["hr"]}</gpxtpx:hr>
                    </gpxtpx:TrackPointExtension>
                    """
            )
            point.extensions.append(gpx_extension_hr)
        gpx_segment.points.append(point)
    return gpx


def parse_points_to_tcx(run_data, run_points_data, sport_type):
    """
    Convert run points data to TCX format.

    Args:
        run_points_data (list of dict): A list of run data points.

    Returns:
        tcx_data (str): TCX data in string format.
    """

    # note that the timestamp of a point is decisecond(分秒)
    fit_start_time = datetime.fromtimestamp(
        run_data.get("startTime") // 1000, tz=timezone.utc
    ).strftime("%Y-%m-%dT%H:%M:%SZ")

    # early timestamp fields in keep's data stands for delta time, but in newly
    # data (or points normalized by _decode_and_process_points for merging)
    # the timestamp field stands for an already-absolute time, so it doesn't
    # need to plus extra start_time. Mirrors the same check in parse_points_to_gpx.
    tcx_start_time = run_data.get("startTime")
    if (
        run_points_data
        and run_points_data[0].get("timestamp", 0) > TIMESTAMP_THRESHOLD_IN_DECISECOND
    ):
        tcx_start_time = 0

    # Root node
    training_center_database = ET.Element(
        "TrainingCenterDatabase",
        {
            "xmlns": "http://www.garmin.com/xmlschemas/TrainingCenterDatabase/v2",
            "xmlns:ns5": "http://www.garmin.com/xmlschemas/ActivityGoals/v1",
            "xmlns:ns3": "http://www.garmin.com/xmlschemas/ActivityExtension/v2",
            "xmlns:ns2": "http://www.garmin.com/xmlschemas/UserProfile/v2",
            "xmlns:xsi": "http://www.w3.org/2001/XMLSchema-instance",
            "xmlns:ns4": "http://www.garmin.com/xmlschemas/ProfileExtension/v1",
            "xsi:schemaLocation": "http://www.garmin.com/xmlschemas/TrainingCenterDatabase/v2 http://www.garmin.com/xmlschemas/TrainingCenterDatabasev2.xsd",
        },
    )
    # xml tree
    ET.ElementTree(training_center_database)
    # Activities
    activities = ET.Element("Activities")
    training_center_database.append(activities)
    # activity
    activity = ET.Element("Activity", {"Sport": sport_type})
    activities.append(activity)
    # Id
    activity_id = ET.Element("Id")
    activity_id.text = fit_start_time  # Keep use start_time as ID
    activity.append(activity_id)
    # Lap
    activity_lap = ET.Element("Lap", {"StartTime": fit_start_time})
    activity.append(activity_lap)
    # TotalTimeSeconds
    activity_total_time = ET.Element("TotalTimeSeconds")
    activity_total_time.text = str(run_data.get("duration"))
    activity_lap.append(activity_total_time)
    # DistanceMeters
    activity_distance = ET.Element("DistanceMeters")
    activity_distance.text = str(run_data.get("distance"))
    activity_lap.append(activity_distance)
    #       Calories
    activity_calories = ET.Element("Calories")
    activity_calories.text = str(run_data.get("calorie"))
    activity_lap.append(activity_calories)
    # Track
    track = ET.Element("Track")
    activity_lap.append(track)
    for point in run_points_data:
        tp = ET.Element("Trackpoint")
        track.append(tp)
        # Time
        # note that the timestamp of a point is decisecond(分秒)
        time_stamp = datetime.fromtimestamp(
            (tcx_start_time // 1000 + point.get("timestamp") // 10),
            tz=timezone.utc,
        ).strftime("%Y-%m-%dT%H:%M:%SZ")
        time_label = ET.Element("Time")
        time_label.text = time_stamp
        tp.append(time_label)
        # Position
        try:
            position = ET.Element("Position")
            tp.append(position)
            #   LatitudeDegrees
            lati = ET.Element("LatitudeDegrees")
            lati.text = str(point["latitude"])
            position.append(lati)
            #   LongitudeDegrees
            longi = ET.Element("LongitudeDegrees")
            longi.text = str(point["longitude"])
            position.append(longi)
            #  AltitudeMeters
            altitude_meters = ET.Element("AltitudeMeters")
            altitude_meters.text = str(point.get("altitude"))
            tp.append(altitude_meters)
        except KeyError:
            pass
        # HeartRateBpm
        try:
            bpm = ET.Element("HeartRateBpm")
            bpm_value = ET.Element("Value")
            bpm.append(bpm_value)
            bpm_value.text = str(point["hr"])
            tp.append(bpm)
        except KeyError:
            pass
    # write to TCX file
    xml_str = minidom.parseString(ET.tostring(training_center_database))
    return xml_str


def find_nearest_hr(
    hr_data_list, target_time, start_time, threshold=HR_FRAME_THRESHOLD_IN_DECISECOND
):
    """
    Find the nearest heart rate data point to the target time.
    if cannot found suitable HR data within the specified time frame (within 10 seconds by default), there will be no hr data return
    Args:
        heart_rate_data (list of dict): A list of heart rate data points, where each point is a dictionary
            containing at least "timestamp" and "beatsPerMinute" keys.
        target_time (float): The target timestamp for which to find the nearest heart rate data point. Please Note that the unit of target_time is decisecond(分秒),
            means 1/10 of a second ,this is very unusual!! so when we convert a target_time to second we need to divide by 10, and when we convert a target time to millisecond
            we need to times 100.
        start_time (float): The reference start time. the unit of start_time is normal millisecond timestamp
        threshold (float, optional): The maximum allowed time difference to consider a data point as the nearest.
            Default is HR_THRESHOLD, the unit is decisecond(分秒)

    Returns:
        int or None: The heart rate value of the nearest data point, or None if no suitable data point is found.
    """
    closest_element = None
    # init difference value
    min_difference = float("inf")
    if target_time > TIMESTAMP_THRESHOLD_IN_DECISECOND:
        # note that the unit of target_time is decisecond and the unit of start_time is normal millisecond
        target_time = target_time = target_time - start_time // 100

    for item in hr_data_list:
        timestamp = item.get("timestamp")

        if not timestamp:
            continue

        difference = abs(timestamp - target_time)

        if difference <= threshold and difference < min_difference:
            closest_element = item
            min_difference = difference

    if closest_element:
        hr = closest_element.get("beatsPerMinute")
        if hr and hr > 0:
            return hr

    return None


def download_keep_gpx(gpx_data, keep_id):
    try:
        print(f"downloading keep_id {str(keep_id)} gpx")
        file_path = os.path.join(GPX_FOLDER, str(keep_id) + ".gpx")
        with open(file_path, "w") as fb:
            fb.write(gpx_data)
        return file_path
    except Exception as e:
        print(f"Something wrong to download keep gpx {str(e)}")
        print(f"wrong id {keep_id}")
        pass


def download_keep_tcx(tcx_data, keep_id):
    try:
        print(f"downloading keep_id {str(keep_id)} tcx")
        file_path = os.path.join(TCX_FOLDER, str(keep_id) + ".tcx")
        with open(file_path, "w") as fb:
            fb.write(tcx_data)
        return file_path
    except Exception as e:
        print(f"Something wrong to download keep tcx {str(e)}")
        print(f"wrong id {keep_id}")
        pass


def run_keep_sync(
    email, password, keep_sports_data_api, with_gpx=False, with_tcx=False
):
    generator = Generator(SQL_FILE)
    old_tracks_ids = generator.get_old_tracks_ids()
    new_tracks = get_all_keep_tracks(
        email, password, old_tracks_ids, keep_sports_data_api, with_gpx, with_tcx
    )
    generator.sync_from_app(new_tracks)

    activities_list = generator.load()
    with open(JSON_FILE, "w") as f:
        json.dump(activities_list, f)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("phone_number", help="keep login phone number")
    parser.add_argument("password", help="keep login password")
    parser.add_argument(
        "--sync-types",
        dest="sync_types",
        nargs="+",
        default=KEEP_SPORT_TYPES,
        help="sync sport types from keep, default is running, you can choose from running, hiking, cycling",
    )
    parser.add_argument(
        "--with-gpx",
        dest="with_gpx",
        action="store_true",
        help="get all keep data to gpx and download",
    )
    parser.add_argument(
        "--with-tcx",
        dest="with_tcx",
        action="store_true",
        help="get all keep data to tcx and download",
    )
    options = parser.parse_args()
    for _tpye in options.sync_types:
        assert (
            _tpye in KEEP_SPORT_TYPES
        ), f"{_tpye} are not supported type, please make sure that the type entered in the {KEEP_SPORT_TYPES}"
    run_keep_sync(
        options.phone_number,
        options.password,
        options.sync_types,
        options.with_gpx,
        options.with_tcx,
    )
