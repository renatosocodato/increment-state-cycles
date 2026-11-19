"""Synthetic benchmark with a known population contrast and a matched null."""

from random import Random
from statistics import mean

from increment_state_cycles.modulation import Track, compare_conditions


def main():
    rng = Random(20261119)
    studies = 250
    for comparison_probability in (0.35, 0.65):
        truth = 2 * (comparison_probability - 0.35)
        estimates = []
        covered = 0
        for study in range(studies):
            tracks = []
            for condition, probability in (("control", 0.35), ("treated", comparison_probability)):
                for unit in range(40):
                    direction = 1 if rng.random() < probability else -1
                    tracks.append(Track(condition, f"{condition}-{unit}",
                                        tuple(direction * i for i in range(5))))
            result = compare_conditions(tracks, "control", "treated", pause_thresholds=(0,),
                                        resamples=999, seed=study)
            q1 = result["grid"][0]["endpoints"]["q1"]
            estimates.append(q1["difference"])
            low, high = q1["interval"]
            covered += low - 1e-12 <= truth <= high + 1e-12
        print(f"truth={truth:.2f} estimate={mean(estimates):.4f} "
              f"coverage={covered}/{studies} ({covered/studies:.1%})")


if __name__ == "__main__":
    main()
