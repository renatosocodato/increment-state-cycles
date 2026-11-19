"""CSV interface for the trajectory contrast estimator."""

import argparse
import csv
import json
from pathlib import Path

from . import contrasts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("csv_file", type=Path, help="CSV with one trajectory per row and a sequence column")
    args = parser.parse_args()
    try:
        with args.csv_file.open(encoding="utf-8-sig", newline="") as handle:
            reader = csv.DictReader(handle, strict=True)
            if (reader.fieldnames or []).count("sequence") != 1:
                raise ValueError("CSV must have exactly one column named sequence.")
            print(json.dumps(contrasts(row["sequence"] for row in reader), indent=2))
    except (OSError, csv.Error, ValueError) as exc:
        parser.error(str(exc))
