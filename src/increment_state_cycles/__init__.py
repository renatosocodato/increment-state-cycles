"""Physical reversal and empirical contrasts for E/P/R increment sequences."""

from collections import Counter
from collections.abc import Iterable

_PARITY = str.maketrans("EPR", "RPE")
_SYMBOLS = frozenset("EPR")

__all__ = ["contrasts", "physical_reverse"]


def _validated(sequence: str) -> str:
    if not isinstance(sequence, str) or not sequence or set(sequence) - _SYMBOLS:
        raise ValueError("Each trajectory must be a nonempty string of E, P and R.")
    return sequence


def physical_reverse(sequence: str) -> str:
    """Reverse increment order and exchange extension and retraction."""
    return _validated(sequence)[::-1].translate(_PARITY)


def contrasts(trajectories: Iterable[str]) -> dict:
    """Pool window counts within trajectories, weighting each eligible window equally.

    These descriptive estimates do not assume stationarity. The finite endpoint
    term, PE-versus-RP contrast, and both denominators are returned explicitly.
    A contrast is None when there are no eligible windows. No uncertainty or
    thermodynamic dissipation estimate is computed.
    """
    if isinstance(trajectories, str):
        raise ValueError("Pass an iterable of trajectories, e.g. ['EPR'].")
    pairs: Counter[str] = Counter()
    lag_two: Counter[str] = Counter()
    triples: Counter[str] = Counter()
    track_count = endpoint_count = 0
    for sequence in trajectories:
        sequence = _validated(sequence)
        track_count += 1
        endpoint_count += (sequence[-1] == "P") - (sequence[0] == "P")
        pairs.update(a + b for a, b in zip(sequence, sequence[1:]))
        lag_two.update(a + b for a, b in zip(sequence, sequence[2:]))
        triples.update(a + b + c for a, b, c in zip(sequence, sequence[1:], sequence[2:]))
    if not track_count:
        raise ValueError("At least one trajectory is required.")
    adjacent_n = sum(pairs.values())
    longer_n = sum(triples.values())
    return {
        "trajectories": track_count,
        "adjacent_windows": adjacent_n,
        "longer_windows": longer_n,
        "q1": (pairs["EE"] - pairs["RR"]) / adjacent_n if adjacent_n else None,
        "q2": (pairs["EP"] - pairs["PR"]) / adjacent_n if adjacent_n else None,
        "q3": (pairs["PE"] - pairs["RP"]) / adjacent_n if adjacent_n else None,
        "pause_endpoint_count": endpoint_count,
        "lag_two": (lag_two["PE"] - lag_two["RP"]) / longer_n if longer_n else None,
        "triple": (triples["PRE"] - triples["REP"]) / longer_n if longer_n else None,
    }
