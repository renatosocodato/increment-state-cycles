"""Exact comparison of stationary pair laws; abstract symbols, no trajectory simulation."""

if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from fractions import Fraction as F
from itertools import product

T = lambda x: [[x[2-j][2-i] for j in range(3)] for i in range(3)]
base = [[F(1, 9) for _ in range(3)] for _ in range(3)]
delta = [[1, -1, 0], [-1, 0, 1], [0, 1, -1]]
other = [[base[i][j] + F(delta[i][j], 36) for j in range(3)] for i in range(3)]
ratio = lambda j: j[0][1]*j[1][2]*j[2][0]/(j[1][0]*j[2][1]*j[0][2])
for j in (base, other):
    assert all(x > 0 for row in j for x in row)
    assert all(sum(j[i]) == sum(j[k][i] for k in range(3)) == F(1, 3) for i in range(3))
    assert all(j[i][k] == j[k][i] for i, k in product(range(3), repeat=2))
    assert ratio(j) == 1
assert T(base) == base and T(other) != other
assert other[0][0] - other[2][2] == F(1, 18)
assert other[0][1] - other[1][2] == -F(1, 18)
print('Exact: equal marginals and zero triangular ratio; second pair law breaks physical reversal; q1=1/18, q2=-1/18.')
