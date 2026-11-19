"""Compare E/P/R contrasts across two conditions in a long-form CSV."""

import argparse
from collections import defaultdict
import csv
import json
from pathlib import Path

from .modulation import Track, compare_conditions

FIELDS = ("condition", "unit", "track", "sample", "position")


def read_tracks(path: Path) -> list[Track]:
    grouped = defaultdict(list)
    with path.open(encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle, strict=True)
        if not all((reader.fieldnames or []).count(field) == 1 for field in FIELDS):
            raise ValueError("CSV must contain condition, unit, track, sample and position columns.")
        for row in reader:
            if any(not row[field] or not row[field].strip() for field in FIELDS):
                raise ValueError(f"Missing value at CSV line {reader.line_num}.")
            key = (row["condition"], row["unit"], row["track"])
            grouped[key].append((int(row["sample"]), float(row["position"])))
    tracks = []
    for key, values in grouped.items():
        values.sort()
        start = values[0][0]
        if any(index != start + offset for offset, (index, _) in enumerate(values)):
            raise ValueError(f"Track {key!r} has duplicate or missing sample indices. Split gaps into separate tracks.")
        tracks.append(Track(key[0], key[1], tuple(position for _, position in values)))
    return tracks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csv_file", type=Path)
    parser.add_argument("--reference", required=True)
    parser.add_argument("--comparison", required=True)
    parser.add_argument("--pause-thresholds", type=float, nargs="+", required=True)
    parser.add_argument("--strides", type=int, nargs="+", default=[1])
    parser.add_argument("--sampling-interval", type=float, default=1.0)
    parser.add_argument("--design", choices=("independent", "paired"), default="independent")
    parser.add_argument("--resamples", type=int, default=2000)
    parser.add_argument("--confidence", type=float, default=0.95)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    options = vars(args)
    path = options.pop("csv_file")
    try:
        print(json.dumps(compare_conditions(read_tracks(path), **options), indent=2, allow_nan=False))
    except (OSError, csv.Error, ValueError) as exc:
        parser.error(str(exc))
