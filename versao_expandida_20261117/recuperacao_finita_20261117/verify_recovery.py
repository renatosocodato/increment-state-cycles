from itertools import product
from pathlib import Path
import numpy as np
import pandas as pd
from finite_recovery import RHO, LENGTH, ETA, NREP, pair_kernel, wilson

for rho in RHO:
    kernel = pair_kernel(rho)
    assert np.all(kernel > 0)
    np.testing.assert_allclose(kernel.sum(axis=1), 1, rtol=0, atol=1e-13)
    np.testing.assert_allclose(np.ones(3) @ kernel / 3, np.ones(3)/3, rtol=0, atol=1e-13)

columns = ['rho', 'n', 'arm']
conditions = list(product(RHO, LENGTH, ('control', 'markov', 'directed')))
replicates = NREP
prefix = ''

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
for key, row in summaries.iterrows():
    rho, n, arm, contrast = key
    values = grouped.get_group(key[:-1])[contrast].to_numpy()
    assert np.all(np.isfinite(values)) and np.all(np.abs(values) <= 1)
    np.testing.assert_allclose(values * (n-2), np.round(values * (n-2)), rtol=0, atol=1e-10)
    assert 0 <= row.threshold <= 1
    hits = np.count_nonzero(np.abs(values) > row.threshold)
    low, high = wilson(hits, replicates)
    assert row.k == hits and row.replicates == replicates
    expected = {'mean': values.mean(), 'sd': values.std(ddof=1)}
    coefficient = (3-2*ETA)/18 if contrast == 'triple' else 1/6
    truth = (1-rho)**2 * (1-ETA)**2 * coefficient if arm == 'directed' else 0
    q025, median, q975 = np.quantile(values, [.025, .5, .975])
    expected.update(truth=truth, q025=q025, median=median, q975=q975,
                    exceed=hits/replicates, exceed_lo=low, exceed_hi=high)
    for name, value in expected.items():
        np.testing.assert_allclose(row[name], value, rtol=0, atol=1e-12, err_msg=f'{key}: {name}')
print('All trajectory IDs, reported estimates and intervals verified conditional on the saved thresholds.')
