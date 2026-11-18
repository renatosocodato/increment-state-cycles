from pathlib import Path
from itertools import product
import sys
import pandas as pd
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'extensao_misturante_20261117'))
from mixing_exact import build,word
from synthetic_calibration import C, estimate, wilson, NS, NREP, B as BOOTSTRAPS
root=Path(__file__).resolve().parent
for control in (True,False):
 T,B,n=build(.2,.25,control);p3=np.array([word(''.join(w),T,B,n) for w in product('EPR',repeat=3)]).reshape(3,3,3)
 q3=np.einsum('ijk,ia,jb,kc->abc',p3,C,C,C)
 q2=np.einsum('ijk,ia,kc->ac',p3,C,C)
 t,l=estimate(q3.reshape(1,27),q2.reshape(1,9),np.linalg.inv(C))
 assert abs(t[0]-(0 if control else .05))<1e-12
 assert abs(l[0]-(0 if control else .06))<1e-12
 print('forward/inverse', 'control' if control else 'directed', round(t[0],9),round(l[0],9))
columns = ['model', 'ncal', 'contrast']
conditions = list(product(('control', 'directed'), NS, ('triple', 'lag2')))
studies = pd.read_csv(root / 'studies.csv', float_precision='round_trip')
individual = studies.set_index(columns + ['study'], verify_integrity=True)
assert set(individual.index) == {(*condition, i) for condition in conditions for i in range(NREP)}
for name in ('min_sv', 'zero_cells', 'boot_valid'):
    assert (studies.groupby(['model', 'ncal', 'study'])[name].nunique(dropna=False) == 1).all()
assert np.all(studies.min_sv > .05) and studies.zero_cells.between(0, 9).all()
assert (studies.zero_cells == np.floor(studies.zero_cells)).all()
assert studies.boot_valid.between(0, 1).all()
np.testing.assert_allclose(studies.boot_valid * BOOTSTRAPS, np.round(studies.boot_valid * BOOTSTRAPS), rtol=0, atol=1e-12)
assert np.isfinite(studies[['raw', 'point', 'oracle_point', 'truth', 'min_sv']]).all().all()
assert studies.raw.abs().le(1).all()


def checked_table(filename, methods):
    table = pd.read_csv(root / filename, float_precision='round_trip')
    indexed = table.set_index(columns + ['method'], verify_integrity=True)
    assert set(indexed.index) == {(*condition, method) for condition in conditions for method in methods}
    return indexed


def compare(row, expected):
    for name, value in expected.items():
        np.testing.assert_allclose(row[name], value, rtol=0, atol=1e-12, err_msg=f'{row.name}: {name}')


summary = checked_table('summary.csv', ('fixed', 'joint', 'oracle'))
plot = checked_table('plot_estimates.csv', ('raw', 'point'))
for key, group in studies.groupby(columns):
    model, ncal, contrast = key
    truth = 0 if model == 'control' else (.05 if contrast == 'triple' else .06)
    np.testing.assert_allclose(group.truth, truth, rtol=0, atol=1e-12)
    for method in ('fixed', 'joint', 'oracle'):
        low, high = group[method+'_lo'], group[method+'_hi']
        valid = group.boot_valid >= .95 if method == 'joint' else np.ones(len(group), dtype=bool)
        assert np.isfinite(low[valid]).all() and np.isfinite(high[valid]).all()
        assert low[~valid].isna().all() and high[~valid].isna().all()
        low, high = low[valid], high[valid]
        assert (low <= high).all()
        selected = group[valid]
        n = len(selected)
        covered = ((low <= truth) & (truth <= high)).sum()
        nonzero = ((low > 0) | (high < 0)).sum()
        clo, chi = wilson(covered, n)
        nlo, nhi = wilson(nonzero, n)
        compare(summary.loc[(*key, method)], dict(
            n=n, abstain=NREP-n, truth=truth, mean_raw=selected.raw.mean(),
            mean_point=selected['oracle_point' if method == 'oracle' else 'point'].mean(),
            coverage=covered/n, coverage_lo=clo, coverage_hi=chi,
            nonzero=nonzero/n, nonzero_lo=nlo, nonzero_hi=nhi,
            mean_width=(high-low).mean(), zero_cal_fraction=(selected.zero_cells > 0).mean(),
            mean_boot_valid=selected.boot_valid.mean()))
    for method in ('raw', 'point'):
        values = group[method]
        mean = values.mean()
        half = 1.96 * values.std(ddof=1) / np.sqrt(len(values))
        compare(plot.loc[(*key, method)], dict(mean=mean, lo=mean-half, hi=mean+half, truth=truth))
print('Independent study IDs, interval estimates, coverage, nonzero rates and figure estimates verified.')
