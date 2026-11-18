from pathlib import Path
import csv, collections
import numpy as np
from finite_recovery import pair_kernel, RHO, LENGTH, NREP
root=Path(__file__).resolve().parent
s=list(csv.DictReader((root/'summary.csv').open())); d=collections.defaultdict(list)
with (root/'trajectories.csv').open() as f:
 for row in csv.DictReader(f): d[(float(row['rho']),int(row['n']),row['arm'])].append((float(row['triple']),float(row['lag2'])))
assert len(d)==len(RHO)*len(LENGTH)*3
for key,rows in d.items(): assert len(rows)==NREP
for rho in RHO:
 k=pair_kernel(rho)
 assert np.allclose(k.sum(axis=1),1) and np.all(k>0)
 assert np.allclose(np.ones(3)/3 @ k, np.ones(3)/3)
for x in s:
 a=np.array(d[(float(x['rho']),int(x['n']),x['arm'])]);v=a[:,0 if x['contrast']=='triple' else 1]
 assert abs(v.mean()-float(x['mean']))<1e-12
 assert abs((abs(v)>float(x['threshold'])).mean()-float(x['exceed']))<1e-12
 assert abs(np.quantile(v,.025)-float(x['q025']))<1e-12
print('Verified counts, stationary matched Markov kernel, summary means, tail quantiles and threshold exceedances.')
