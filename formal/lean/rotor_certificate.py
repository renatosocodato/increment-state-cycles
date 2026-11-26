"""Independent exact interval check for the CTMC rotor at gamma=1.

The Poisson series is truncated at 12. The omitted (unnormalized)
mass is bounded by the first omitted term times a geometric majorant.
No floating-point operation enters the sign decisions.
"""
from fractions import Fraction as Q
from dataclasses import dataclass
from math import factorial
import json


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = (self.lo * other.lo, self.lo * other.hi, self.hi * other.lo, self.hi * other.hi)
        return Interval(min(products), max(products))


def exact(n):
    return Interval(Q(n), Q(n))


ZERO, ONE = exact(0), exact(1)
MARKER = (0, 1, 1, 0, 1, 0)
N = 12


def kernel(u, a):
    """Enclose the six probabilities for net displacement modulo six."""
    assert 0 < u < N + 2 and -1 <= a.lo <= a.hi <= 1
    p, m = (ONE + a) * exact(Q(1, 2)), (ONE - a) * exact(Q(1, 2))
    walk = [ONE, ZERO, ZERO, ZERO, ZERO, ZERO]
    partial = walk.copy()
    total = Q(1)
    for n in range(1, N + 1):
        walk = [walk[(j - 1) % 6] * p + walk[(j + 1) % 6] * m for j in range(6)]
        weight = Q(u**n, factorial(n))
        total += weight
        partial = [x + y * exact(weight) for x, y in zip(partial, walk)]
    tail = Q(u**(N + 1), factorial(N + 1)) / (1 - Q(u, N + 2))
    return tuple(Interval(x.lo / (total + tail), (x.hi + tail) / total) for x in partial)


def correlation(k):
    return sum((k[d] * exact(Q(sum(1 if MARKER[i] == MARKER[(i + d) % 6] else -1
                                 for i in range(6)), 6)) for d in range(6)), ZERO)


def residual(a):
    r1 = correlation(kernel(1, a))
    return correlation(kernel(2, a)) - r1 * r1


def word(k, bits):
    """Sum every hidden path consistent with the four observed positions."""
    pos = [[i for i, marker in enumerate(MARKER) if marker == digit] for digit in bits]
    return sum((k[(j-i) % 6] * k[(l-j) % 6] * k[(m-l) % 6] * exact(Q(1, 6))
                for i in pos[0] for j in pos[1] for l in pos[2] for m in pos[3]), ZERO)


def main():
    if not __debug__:
        raise SystemExit("Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.")
    lo, hi = Q(52363, 100000), Q(52365, 100000)
    left, right = residual(exact(lo)), residual(exact(hi))
    box = kernel(1, Interval(lo, hi))
    delta = word(box, (1, 1, 0, 1)) - word(box, (1, 0, 1, 1))
    r1 = correlation(box)
    assert left.lo > 0 and right.hi < 0 and delta.lo > Q(23, 10000)
    assert 0 < r1.lo <= r1.hi < 1
    # The suppressed jump counts are uniform in a. The series is continuous
    # by its uniform geometric tail, so the intermediate value theorem applies.
    out = {"a": [float(lo), float(hi)]}
    for name, x in (("residual_left", left), ("residual_right", right),
                    ("delta3_whole_bracket", delta), ("r1_whole_bracket", r1)):
        out[name] = {"display": [float(x.lo), float(x.hi)], "exact": [str(x.lo), str(x.hi)]}
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
