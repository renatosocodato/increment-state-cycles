import json
from pathlib import Path
import subprocess
import unittest

from increment_state_cycles import contrasts, physical_reverse


class ContrastTests(unittest.TestCase):
    def test_reversal(self):
        original = "EPRERP"
        reversed_track = physical_reverse(original)
        self.assertEqual(reversed_track, "PEREPR")
        self.assertEqual(physical_reverse(reversed_track), original)
        forward = contrasts([original])
        backward = contrasts([reversed_track])
        for key in ("q1", "q2", "q3", "lag_two", "triple"):
            self.assertAlmostEqual(forward[key], -backward[key])

    def test_does_not_join_tracks(self):
        stats = contrasts(["P", "RE"])
        self.assertEqual(stats["adjacent_windows"], 1)
        self.assertIsNone(stats["triple"])
        self.assertIsNone(stats["lag_two"])
        self.assertIsNone(contrasts(["E"])["q1"])

    def test_finite_endpoint_identity(self):
        stats = contrasts(["EEP", "RPE", "EP", "PEE"])
        self.assertAlmostEqual(
            (stats["q2"] - stats["q3"]) * stats["adjacent_windows"],
            stats["pause_endpoint_count"],
        )

    def test_exact_phased_cycle_from_paper(self):
        cycle = "EPRERP"
        doubled = cycle * 2
        stats = contrasts([doubled[i:i + 3] for i in range(6)])
        self.assertEqual(stats["q1"], 0)
        self.assertEqual(stats["q2"], 0)
        self.assertAlmostEqual(stats["triple"], 1 / 6)
        self.assertAlmostEqual(stats["lag_two"], 1 / 6)

    def test_invalid_input(self):
        for values in ([], ["EX"], [""], "EPR"):
            with self.subTest(values=values), self.assertRaises(ValueError):
                contrasts(values)

    def test_cli_matches_api(self):
        example = Path(__file__).resolve().parents[1] / "examples/synthetic_trajectories.csv"
        result = subprocess.check_output(["increment-state-cycles", str(example)], text=True)
        self.assertEqual(json.loads(result), contrasts(example.read_text().splitlines()[1:]))
