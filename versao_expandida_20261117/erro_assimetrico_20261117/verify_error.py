
if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from itertools import product
from pathlib import Path
import numpy as np
import pandas as pd
from finite_error import RHO, LENGTH, DELTAS, NR, wilson
from mixing_exact import build, word
from asymmetric_exact import channel

for rho in RHO:
    for alpha, beta in ((0, .16), (.08, .08), (.16, 0)):
        laws = []
        for control in (False, True):
            transition, emission, n = build(rho, .25, control)
            emission = channel(emission, alpha, beta)
            laws.append([word(a+b, transition, emission, n) for a, b in product('EPR', repeat=2)])
        np.testing.assert_allclose(laws[0], laws[1], rtol=0, atol=1e-13)
        np.testing.assert_allclose(sum(laws[0]), 1, rtol=0, atol=1e-13)

columns = ['rho', 'n', 'delta']
conditions = list(product(RHO, LENGTH, DELTAS))
replicates = NR
prefix = 'finite_'

root = Path(__file__).resolve().parent
raw = pd.read_csv(root / (prefix+'trajectories.csv'), float_precision='round_trip')
summary = pd.read_csv(root / (prefix+'summary.csv'), float_precision='round_trip')
trajectories = raw.set_index(columns + ['replicate'], verify_integrity=True)
assert set(trajectories.index) == {(*condition, i) for condition in conditions for i in range(replicates)}
summaries = summary.set_index(columns + ['contrast'], verify_integrity=True)
assert set(summaries.index) == {(*condition, s) for condition in conditions for s in ('triple', 'lag2')}
# Each condition family was evaluated with one independently calibrated threshold per contrast.
assert (summary.groupby(['rho', 'n', 'contrast']).threshold.nunique(dropna=False) == 1).all()
grouped = raw.groupby(columns)
max_standard_errors = 0.0
for key, row in summaries.iterrows():
    rho, n, delta, contrast = key
    values = grouped.get_group(key[:-1])[contrast].to_numpy()
    assert np.all(np.isfinite(values)) and np.all(np.abs(values) <= 1)
    np.testing.assert_allclose(values * (n-2), np.round(values * (n-2)), rtol=0, atol=1e-10)
    assert 0 <= row.threshold <= 1
    hits = np.count_nonzero(np.abs(values) > row.threshold)
    low, high = wilson(hits, replicates)
    assert row.k == hits and row.replicates == replicates
    expected = {'mean': values.mean(), 'sd': values.std(ddof=1)}
    attenuation = (1-rho)**2 * .75**2
    truth = 0 if contrast == 'triple' else -delta*(4-attenuation)/18
    deviation = abs(values.mean()-truth) / (values.std(ddof=1) / np.sqrt(replicates))
    max_standard_errors = max(max_standard_errors, deviation)
    expected.update(rate=hits/replicates, lo=low, hi=high)
    for name, value in expected.items():
        np.testing.assert_allclose(row[name], value, rtol=0, atol=1e-12, err_msg=f'{key}: {name}')
print('All trajectory IDs, reported estimates and intervals verified conditional on the saved thresholds.')
print('Maximum mean deviation from the exact law in Monte Carlo standard errors:', round(max_standard_errors, 3))
