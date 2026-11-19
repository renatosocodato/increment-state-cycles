"""Compare condition means of E/P/R contrasts at the experimental-unit level."""

from collections import defaultdict
from collections.abc import Iterable
from dataclasses import dataclass
import math
from random import Random
from statistics import fmean as mean

from . import contrasts

ENDPOINTS = ("q1", "q2", "q3", "lag_two", "triple")


@dataclass(frozen=True)
class Track:
    """A contiguous, regularly sampled trajectory of an even coordinate."""

    condition: str
    unit: str
    positions: tuple[float, ...]


def symbolise(positions: Iterable[float], pause_threshold: float, stride: int = 1) -> str:
    """Resample from the first position, then code increments with an inclusive pause band."""
    if not math.isfinite(pause_threshold) or pause_threshold < 0:
        raise ValueError("pause_threshold must be finite and nonnegative.")
    if type(stride) is not int or stride < 1:
        raise ValueError("stride must be a positive integer.")
    positions = tuple(positions)
    if not positions or not all(map(math.isfinite, positions)):
        raise ValueError("Each track must contain finite positions.")
    sampled = positions[::stride]
    symbols = []
    for start, end in zip(sampled, sampled[1:]):
        delta = end - start
        symbols.append("E" if delta > pause_threshold else "R" if delta < -pause_threshold else "P")
    return "".join(symbols)


def _quantile(values, probability):
    index = probability * (len(values) - 1)
    low = math.floor(index)
    high = math.ceil(index)
    return values[low] + (index - low) * (values[high] - values[low])


def _bootstrap(reference, comparison, paired, resamples, confidence, seed):
    if min(len(reference), len(comparison)) < 2:
        return None
    rng = Random(seed)
    if paired:
        values = [b - a for a, b in zip(reference, comparison)]
        draws = [mean(rng.choices(values, k=len(values))) for _ in range(resamples)]
    else:
        draws = [
            mean(rng.choices(comparison, k=len(comparison)))
            - mean(rng.choices(reference, k=len(reference)))
            for _ in range(resamples)
        ]
    draws.sort()
    tail = (1 - confidence) / 2
    return [_quantile(draws, tail), _quantile(draws, 1 - tail)]


def compare_conditions(
    tracks: Iterable[Track],
    reference: str,
    comparison: str,
    *,
    pause_thresholds: Iterable[float],
    strides: Iterable[int] = (1,),
    sampling_interval: float = 1.0,
    design: str = "independent",
    resamples: int = 2000,
    confidence: float = 0.95,
    seed: int = 0,
) -> dict:
    """Estimate comparison minus reference on a fixed threshold/stride grid.

    Pool eligible windows within each unit and give units equal weight.
    Bootstrap independent units or matched unit pairs. Intervals are pointwise.
    """
    if not reference or not comparison or reference == comparison:
        raise ValueError("Supply two distinct condition names.")
    if design not in ("independent", "paired"):
        raise ValueError("design must be independent or paired.")
    if not math.isfinite(sampling_interval) or sampling_interval <= 0:
        raise ValueError("sampling_interval must be finite and positive.")
    if type(resamples) is not int or resamples < 2 or not 0 < confidence < 1:
        raise ValueError("Use at least two bootstrap resamples and confidence between 0 and 1.")
    if type(seed) is not int:
        raise ValueError("seed must be an integer.")
    thresholds, strides = tuple(pause_thresholds), tuple(strides)
    if not thresholds or not strides:
        raise ValueError("Provide at least one pause threshold and one stride.")
    for threshold in thresholds:
        if not math.isfinite(threshold) or threshold < 0:
            raise ValueError("Pause thresholds must be finite and nonnegative.")
    for stride in strides:
        if type(stride) is not int or stride < 1 or not math.isfinite(sampling_interval * stride):
            raise ValueError("Strides must be positive integers with finite effective intervals.")
    if len(set(thresholds)) != len(thresholds) or len(set(strides)) != len(strides):
        raise ValueError("Grid settings must be unique.")

    grouped = {reference: defaultdict(list), comparison: defaultdict(list)}
    for track in tracks:
        if track.condition not in grouped:
            raise ValueError(f"Unexpected condition {track.condition!r}.")
        if not isinstance(track.unit, str) or not track.unit.strip():
            raise ValueError("Each track must have a nonempty experimental-unit ID.")
        positions = tuple(track.positions)
        if not positions or not all(map(math.isfinite, positions)):
            raise ValueError("Each track must contain finite positions.")
        grouped[track.condition][track.unit].append(positions)
    if not all(grouped.values()):
        raise ValueError("Both conditions must contain tracks.")
    if design == "independent" and grouped[reference].keys() & grouped[comparison].keys():
        raise ValueError("Unit IDs overlap between conditions. Use paired design for repeated units.")
    if design == "paired" and grouped[reference].keys() != grouped[comparison].keys():
        raise ValueError("Paired design requires the same experimental-unit IDs in both conditions.")

    results = []
    for threshold in thresholds:
        for stride in strides:
            estimates = {}
            for condition, units in grouped.items():
                estimates[condition] = {}
                for unit, trajectories in sorted(units.items()):
                    sequences = [symbolise(track, threshold, stride) for track in trajectories]
                    eligible = [sequence for sequence in sequences if sequence]
                    estimates[condition][unit] = contrasts(eligible) if eligible else dict.fromkeys(ENDPOINTS)
            endpoints = {}
            for endpoint in ENDPOINTS:
                by_condition = {
                    condition: {unit: stats[endpoint] for unit, stats in units.items()
                                if stats[endpoint] is not None}
                    for condition, units in estimates.items()
                }
                a, b = by_condition[reference], by_condition[comparison]
                if design == "paired":
                    matched = sorted(a.keys() & b.keys())
                    a = {unit: a[unit] for unit in matched}
                    b = {unit: b[unit] for unit in matched}
                values_a, values_b = list(a.values()), list(b.values())
                mean_a = mean(values_a) if values_a else None
                mean_b = mean(values_b) if values_b else None
                endpoints[endpoint] = {
                    "reference_mean": mean_a,
                    "comparison_mean": mean_b,
                    "difference": mean_b - mean_a if a and b else None,
                    "interval": _bootstrap(values_a, values_b, design == "paired",
                                           resamples, confidence, seed),
                    "reference_units_used": list(a),
                    "comparison_units_used": list(b),
                }
            results.append({
                "pause_threshold": threshold,
                "stride": stride,
                "effective_sampling_interval": sampling_interval * stride,
                "endpoints": endpoints,
            })
    return {
        "reference": reference,
        "comparison": comparison,
        "design": design,
        "confidence": confidence,
        "resamples": resamples,
        "seed": seed,
        "unit_counts": {condition: len(units) for condition, units in grouped.items()},
        "grid": results,
    }
