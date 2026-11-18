#!/usr/bin/env python3
"""Check the frozen rotor recovery tables without resimulating."""
from pathlib import Path
import json
import numpy as np
import pandas as pd
p=Path(__file__).resolve().parent/'recuperacao_fisica_20261118'
a=pd.read_csv(p/'estudos_independentes.csv'); s=pd.read_csv(p/'resumo_recuperacao.csv'); m=json.loads((p/'parametros_e_verificacoes.json').read_text())
assert m['seed']==2026111803 and m['max_pair_mismatch']<1e-12
assert len(a)==3*4*600 and len(s)==3*3
for n in m['windows_per_trajectory']:
 group=a[a.windows_per_trajectory==n]
 cal=group[group.group=='calibration_control'].contrast.to_numpy()
 assert len(cal)==600
 threshold=np.quantile(np.abs(cal),.95,method='higher')
 for arm in ('test_control','test_driven','test_reversed_drive'):
  x=group[group.group==arm].contrast.to_numpy();row=s[(s.windows_per_trajectory==n)&(s.model==arm)].iloc[0]
  assert len(x)==600
  assert np.isclose(row['threshold'],threshold,rtol=0,atol=1e-14)
  assert np.isclose(row['mean'],x.mean(),rtol=0,atol=1e-14)
  assert row['exceedances']==np.count_nonzero(abs(x)>threshold)
  assert np.isclose(row['repeat_lo'],np.quantile(x,.025),atol=1e-14)
  assert np.isclose(row['repeat_hi'],np.quantile(x,.975),atol=1e-14)
print('Rotor frozen-calibration thresholds, means, intervals and independent-study counts verified.')
