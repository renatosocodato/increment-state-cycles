#!/usr/bin/env python3
"""Independent synthetic finite-trajectory study; frozen design in PLANO_ANTES_DA_SIMULACAO.md."""

if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from pathlib import Path
from itertools import product
import json
import numpy as np
import pandas as pd
from scipy.linalg import expm
from scipy.optimize import brentq

ROOT=Path(__file__).resolve().parent
WINDOWS=(256,1024,4096)
STUDIES=600
TRAJECTORIES=24
SEED=2026111803
MARKER=np.array([0,1,1,0,1,0],dtype=np.int8)
SIGNS=('E','P','R')

def corr(u,a):
 return (2/9*np.exp(-u/2)+2/3*np.exp(-3*u/2))*np.cos(np.sqrt(3)*a*u/2)+np.exp(-2*u)/9

def ring_transition(a):
 q=np.zeros((6,6))
 for i in range(6):
  q[i,(i+1)%6]=(1+a)/2; q[i,(i-1)%6]=(1-a)/2; q[i,i]=-1
 return expm(q)

def pair_and_triple(P,x):
 n=len(x);dif=x[None,:]-x[:,None]
 mats={label:P*(dif==v) for label,v in [('E',1),('P',0),('R',-1)]}
 def prob(word):
  v=np.ones(n)/n
  for letter in word:v=v@mats[letter]
  return float(v.sum())
 J=np.array([[prob(a+b) for b in SIGNS] for a in SIGNS])
 return J,prob('PRE')-prob('REP'),prob('PRE'),prob('REP')

def samples(P,x,seedseq,is_control=False):
 rng=np.random.default_rng(seedseq)
 shape=(STUDIES,TRAJECTORIES)
 n=len(x);state=rng.integers(n,size=shape,dtype=np.int8)
 if is_control:
  flip=float(P[0,1])
  def step(s):return np.bitwise_xor(s,rng.random(shape)<flip).astype(np.int8)
 else:
  cdf=np.cumsum(P[0]);cdf[-1]=1.0
  assert all(np.allclose(P[i],np.roll(P[0],i),atol=1e-13) for i in range(n))
  def step(s):return ((s+np.searchsorted(cdf,rng.random(shape)))%n).astype(np.int8)
 x0=x[state];state=step(state);x1=x[state];state=step(state);x2=x[state]
 numer=np.zeros(STUDIES,dtype=np.int64);allout={}
 for w in range(1,max(WINDOWS)+1):
  state=step(state);x3=x[state]
  p=(x0==1)&(x1==1)&(x2==0)&(x3==1)
  r=(x0==1)&(x1==0)&(x2==1)&(x3==1)
  numer+=np.count_nonzero(p,axis=1)-np.count_nonzero(r,axis=1)
  x0,x1,x2=x1,x2,x3
  if w in WINDOWS:allout[w]=numer.copy()/(TRAJECTORIES*w)
 return allout

def wilson(k,n,z=1.959963984540054):
 p=k/n;den=1+z*z/n;c=(p+z*z/(2*n))/den
 h=z*np.sqrt(p*(1-p)/n+z*z/(4*n*n))/den
 return max(0.,c-h),min(1.,c+h)

# Verify that position words map exactly to the stated physical increment symbols.
def symbols(x):return ''.join('E' if b>a else 'R' if b<a else 'P' for a,b in zip(x,x[1:]))
assert symbols([1,1,0,1])=='PRE' and symbols([1,0,1,1])=='REP'
a=brentq(lambda v:corr(2,v)-corr(1,v)**2,0,.999,xtol=1e-14)
P=ring_transition(a);Pr=ring_transition(-a);f=(1-corr(1,a))/2
Pc=np.array([[1-f,f],[f,1-f]])
assert 0<f<.5 and np.allclose(P.sum(axis=1),1) and np.all(P>=0)
assert np.allclose(np.ones(6)@P/6,np.ones(6)/6) and np.allclose(Pc,Pc.T)
J,D,p_pre,p_rep=pair_and_triple(P,MARKER)
Jr,Dr,_,_=pair_and_triple(Pr,MARKER)
Jc,Dc,_,_=pair_and_triple(Pc,np.array([0,1],dtype=np.int8))
assert np.max(abs(J-Jc))<1e-12 and np.max(abs(J-Jr))<1e-12
assert abs(D+Dr)<1e-12 and abs(Dc)<1e-12 and D>0
streams=np.random.SeedSequence(SEED).spawn(4)
arrays={
 'calibration_control':samples(Pc,np.array([0,1],dtype=np.int8),streams[0],True),
 'test_control':samples(Pc,np.array([0,1],dtype=np.int8),streams[1],True),
 'test_driven':samples(P,MARKER,streams[2]),
 'test_reversed_drive':samples(Pr,MARKER,streams[3]),
}
raw=[];summary=[]
for w in WINDOWS:
 threshold=float(np.quantile(abs(arrays['calibration_control'][w]),.95,method='higher'))
 for label in ('test_control','test_driven','test_reversed_drive'):
  scores=arrays[label][w];events=int(np.count_nonzero(abs(scores)>threshold));lo,hi=wilson(events,STUDIES)
  truth={'test_control':0.,'test_driven':D,'test_reversed_drive':Dr}[label]
  summary.append({'windows_per_trajectory':w,'trajectories_per_study':TRAJECTORIES,'studies':STUDIES,'model':label,
                  'expected':truth,'mean':float(scores.mean()),'median':float(np.median(scores)),
                  'repeat_lo':float(np.quantile(scores,.025)),'repeat_hi':float(np.quantile(scores,.975)),
                  'threshold':threshold,'exceedances':events,'exceedance_fraction':events/STUDIES,
                  'wilson_low':lo,'wilson_high':hi})
 for label in arrays:
  for i,v in enumerate(arrays[label][w]):raw.append({'windows_per_trajectory':w,'group':label,'study':i,'contrast':v})
pd.DataFrame(raw).to_csv(ROOT/'estudos_independentes.csv',index=False)
pd.DataFrame(summary).to_csv(ROOT/'resumo_recuperacao.csv',index=False)
meta={'seed':SEED,'calibration_studies_per_length':STUDIES,'test_studies_per_model_and_length':STUDIES,
      'independent_trajectories_per_study':TRAJECTORIES,'lengths_are_nested':True,'windows_per_trajectory':WINDOWS,
      'bias':a,'rates_per_sample':[(1+a)/2,(1-a)/2],'control_flip_per_sample':f,
      'pair_matrix':J.tolist(),'max_pair_mismatch':float(np.max(abs(J-Jc))),
      'expected_contrasts':{'driven':D,'opposite':Dr,'equilibrium':Dc},
      'driven_PRE':p_pre,'driven_REP':p_rep,'observations':'synthetic ideal measurement; quantile calibration is conditional and model-specific'}
(ROOT/'parametros_e_verificacoes.json').write_text(json.dumps(meta,indent=2)+'\n')
print('parameters:',json.dumps(meta,ensure_ascii=False))
print(pd.DataFrame(summary).round(5).to_string(index=False))
