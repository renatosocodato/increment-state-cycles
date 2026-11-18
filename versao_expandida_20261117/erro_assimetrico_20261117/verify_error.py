from pathlib import Path
from collections import defaultdict
import csv,sys
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'extensao_misturante_20261117'))
from mixing_exact import build,word
from asymmetric_exact import channel
root=Path(__file__).resolve().parent
for rho in [.2,.65]:
 for alpha,beta in [(0,.16),(.08,.08),(.16,0)]:
  laws=[]
  for ctrl in [False,True]:
   T,B,n=build(rho,.25,ctrl);B=channel(B,alpha,beta)
   laws.append(np.array([word(a+b,T,B,n) for a in 'EPR' for b in 'EPR']))
  assert np.allclose(laws[0],laws[1],atol=1e-13) and np.isclose(sum(laws[0]),1)
groups=defaultdict(list)
for row in csv.DictReader((root/'finite_trajectories.csv').open()):groups[(float(row['rho']),int(row['n']),float(row['delta']))].append((float(row['triple']),float(row['lag2'])))
assert len(groups)==20 and all(len(v)==2000 for v in groups.values())
maxz=0
for x in csv.DictReader((root/'finite_summary.csv').open()):
 vals=np.array(groups[(float(x['rho']),int(x['n']),float(x['delta']))])[:,0 if x['contrast']=='triple' else 1]
 assert abs(vals.mean()-float(x['mean']))<1e-12
 assert abs((abs(vals)>float(x['threshold'])).mean()-float(x['rate']))<1e-12
 rho=float(x['rho']);d=float(x['delta']);k=(1-rho)**2*.75**2
 truth=0 if x['contrast']=='triple' else -d*(4-k)/18
 maxz=max(maxz,abs(vals.mean()-truth)/(vals.std(ddof=1)/np.sqrt(len(vals))))
print('Matched pair laws, complete counts and summary reconstruction checked; max MC mean deviation in SE:',round(maxz,3))
