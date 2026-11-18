"""Exact arithmetic checks for the parity note; no simulation or file writes."""
from collections import Counter
from fractions import Fraction as F
from itertools import product

E, P, R = range(3)
eps = (R, P, E)


def pair_table(parent, pi, label):
    table = [[F(0) for _ in range(3)] for _ in range(3)]
    for a, b, c in product(range(3), repeat=3):
        table[label(a, b)][label(b, c)] += pi[a] * parent[a][b] * parent[b][c]
    return table


def reverse(table):
    return [[table[eps[j]][eps[i]] for j in range(3)] for i in range(3)]


def ratio(j):
    return j[E][P] * j[P][R] * j[R][E] / (j[P][E] * j[R][P] * j[E][R])


def odd(j):
    return (j[E][E] - j[R][R], j[E][P] - j[P][R], j[P][E] - j[R][P])


parent = [[F(7, 10), F(3, 10), F(0)],
          [F(1, 10), F(3, 10), F(6, 10)],
          [F(0), F(2, 10), F(8, 10)]]
pi = [F(1, 13), F(3, 13), F(9, 13)]
assert all(sum(row) == 1 for row in parent)
assert all(pi[a] * parent[a][b] == pi[b] * parent[b][a]
           for a, b in product(range(3), repeat=2))
sign = lambda a, b: E if b > a else R if b < a else P
j = pair_table(parent, pi, sign)
assert j == [[F(x, 1300) for x in row]
             for row in [[18, 153, 39], [75, 652, 153], [117, 75, 18]]]
assert j == reverse(j) and ratio(j) == F(7803, 625)
assert j[E][P] - j[P][E] == j[P][R] - j[R][P] == j[R][E] - j[E][R] == F(78, 1300)

ring = [[F(1, 4), F(1, 2), F(1, 4)],
        [F(1, 4), F(1, 4), F(1, 2)],
        [F(1, 2), F(1, 4), F(1, 4)]]
step = lambda a, b: P if a == b else E if b == (a + 1) % 3 else R
j = pair_table(ring, [F(1, 3)] * 3, step)
p = [F(1, 2), F(1, 4), F(1, 4)]
assert j == [[a * b for b in p] for a in p]
assert ratio(j) == ratio(reverse(j)) == 1
assert odd(j) == (F(3, 16), F(1, 16), F(1, 16))

word = (E, P, R, E, R, P)
n = len(word)
pairs = Counter((word[i], word[(i + 1) % n]) for i in range(n))
triples = Counter(tuple(word[(i + k) % n] for k in range(3)) for i in range(n))
assert all(pairs[(a, b)] == pairs[(eps[b], eps[a])]
           for a, b in product(range(3), repeat=2))
assert triples[(P, R, E)] == 1 and triples[(R, E, P)] == 0
assert sum({E: 1, P: 0, R: -1}[s] for s in word) == 0

for word in product(range(3), repeat=7):
    counts = Counter(zip(word, word[1:]))
    assert ((counts[(E, P)] - counts[(P, R)])
            - (counts[(P, E)] - counts[(R, P)])
            == (word[-1] == P) - (word[0] == P))
print('Exact parent tables, parity, cycle ratios, periodic blind spot and 2187 endpoint identities verified.')
