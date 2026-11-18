from pathlib import Path
from itertools import product
from collections import defaultdict
import csv,sys
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'extensao_misturante_20261117'))
from mixing_exact import build,word
from synthetic_calibration import C,estimate
root=Path(__file__).resolve().parent
for control in (True,False):
 T,B,n=build(.2,.25,control);p3=np.array([word(''.join(w),T,B,n) for w in product('EPR',repeat=3)]).reshape(3,3,3)
 q3=np.einsum('ijk,ia,jb,kc->abc',p3,C,C,C)
 q2=np.einsum('ijk,ia,kc->ac',p3,C,C)
 t,l=estimate(q3.reshape(1,27),q2.reshape(1,9),np.linalg.inv(C))
 assert abs(t[0]-(0 if control else .05))<1e-12
 assert abs(l[0]-(0 if control else .06))<1e-12
 print('forward/inverse', 'control' if control else 'directed', round(t[0],9),round(l[0],9))
rows=list(csv.DictReader((root/'studies.csv').open()));groups=defaultdict(list)
for r in rows:groups[(r['model'],int(r['ncal']),r['contrast'])].append(r)
assert len(groups)==12 and all(len(v)==200 for v in groups.values())
for s in csv.DictReader((root/'summary.csv').open()):
 group=groups[(s['model'],int(s['ncal']),s['contrast'])];meth=s['method']
 valid=[r for r in group if np.isfinite(float(r[meth+'_lo']))]
 coverage=np.mean([float(r[meth+'_lo'])<=float(r['truth'])<=float(r[meth+'_hi']) for r in valid])
 assert abs(coverage-float(s['coverage']))<1e-12
print('Independent 1200-study count, summary coverage and inverse-channel orientation verified.')
print('C singular values:', np.linalg.svd(C,compute_uv=False))
