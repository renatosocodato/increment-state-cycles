import csv
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from increment_state_cycles.modulation import Track, compare_conditions, symbolise


def compare(tracks, **options):
    return compare_conditions(tracks, "control", "treated",
                              pause_thresholds=(0,), resamples=99, **options)["grid"][0]["endpoints"]


class ModulationTests(unittest.TestCase):
    def test_threshold_applies_to_resampled_displacement(self):
        track = (0, 0.5, 1, 1.5, 2)
        self.assertEqual(symbolise(track, 0.5), "PPPP")
        self.assertEqual(symbolise(track, 0.5, 2), "EE")
        self.assertEqual(symbolise(track[::-1], 0.5, 2), "RR")

    def test_equal_weight_per_unit(self):
        tracks = [Track("control", "A", (0, 1, 2, 3))] * 100
        tracks += [Track("control", "B", (3, 2, 1, 0)),
                   Track("treated", "C", (0, 1, 2)),
                   Track("treated", "D", (0, 1, 2))]
        q1 = compare(tracks)["q1"]
        self.assertEqual(q1["reference_mean"], 0)
        self.assertEqual(q1["difference"], 1)
        self.assertEqual(q1["interval"], [0, 2])
        self.assertEqual(q1["reference_units_used"], ["A", "B"])

    def test_paired_bootstrap_preserves_shared_unit_variation(self):
        tracks = [Track(condition, unit, positions)
                  for condition in ("control", "treated")
                  for unit, positions in (("A", (0, 1, 2)), ("B", (2, 1, 0)))]
        self.assertEqual(compare(tracks, design="paired")["q1"]["interval"], [0, 0])
        with self.assertRaisesRegex(ValueError, "overlap"):
            compare(tracks)
        with self.assertRaisesRegex(ValueError, "same experimental-unit IDs"):
            compare(tracks[:-1], design="paired")

    def test_short_tracks_are_not_glued_and_matching_is_endpoint_specific(self):
        tracks = [Track("control", "A", (0, 1))] * 10
        tracks += [Track("treated", "A", (0, 1, 2, 3)),
                   Track("control", "B", (3, 2, 1, 0)),
                   Track("treated", "B", (0, 1, 2, 3))]
        result = compare(tracks, design="paired")
        self.assertEqual(result["q1"]["reference_units_used"], ["B"])
        self.assertEqual(result["q1"]["difference"], 2)
        self.assertIsNone(result["q1"]["interval"])
        self.assertEqual(result["triple"]["comparison_units_used"], ["B"])

    def test_cli_grid_and_gap_rejection(self):
        with tempfile.TemporaryDirectory() as work:
            path = Path(work) / "positions.csv"
            rows = [(condition, str(i), "track", n, p)
                    for i, (condition, direction) in enumerate(
                        (("control", -1), ("control", -1), ("treated", 1), ("treated", 1)))
                    for n, p in enumerate(j * direction / 2 for j in range(5))]
            def run(rows):
                with path.open("w", newline="") as file:
                    writer = csv.writer(file)
                    writer.writerow(("condition", "unit", "track", "sample", "position"))
                    writer.writerows(rows)
                return subprocess.run(
                    ["increment-state-cycles-compare", str(path), "--reference", "control",
                     "--comparison", "treated", "--pause-thresholds", "0", "0.5",
                     "--strides", "1", "2", "--sampling-interval", "0.25", "--resamples", "99"],
                    capture_output=True, text=True
                )

            result = run(rows)
            self.assertEqual(result.returncode, 0, result.stderr)
            grid = json.loads(result.stdout)["grid"]
            self.assertEqual([row["endpoints"]["q1"]["difference"] for row in grid], [2, 2, 0, 2])
            self.assertEqual([row["effective_sampling_interval"] for row in grid], [0.25, 0.5, 0.25, 0.5])
            gap = run(rows[:1] + rows[2:])
            self.assertNotEqual(gap.returncode, 0)
            self.assertIn("missing sample indices", gap.stderr)
