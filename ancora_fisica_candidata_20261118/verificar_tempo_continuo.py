
if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
import numpy as np
from scipy.linalg import expm
from scipy.optimize import brentq
from itertools import product
x=np.array([0,1,1,0,1,0]);X=np.eye(6);half=np.ones(6)/6
states=['E','P','R']
def matrices(T):
 return {s:T*((x[None,:]-x[:,None] == (1 if s=='E' else -1 if s=='R' else 0))) for s in states}
def word(M,w):
 v=half.copy()
 for s in w:v=v@M[s]
 return float(v.sum())
def measures(gamma,a):
 kp=gamma*(1+a)/2;km=gamma*(1-a)/2
 L=np.zeros((6,6))
 for i in range(6):L[i,(i+1)%6]=kp;L[i,(i-1)%6]=km;L[i,i]=-gamma
 T=expm(L);D=matrices(T);J=np.array([[word(D,a+b) for b in states] for a in states]);f=2*float(half @ ((x==0)[:,None]*T*(x[None,:]==1)) @ np.ones(6));ctrl=np.array([[1-f,f],[f,1-f]]);z=np.array([0,1]);C={s:ctrl*((z[None,:]-z[:,None] == (1 if s=='E' else -1 if s=='R' else 0))) for s in states}
 def cw(w):
  v=np.ones(2)/2
  for s in w:v=v@C[s]
  return float(v.sum())
 Jc=np.array([[cw(a+b) for b in states] for a in states]);delta=word(D,'PRE')-word(D,'REP')
 return J,Jc,delta,f
for gamma in [0.25,0.5,1.0]:
 print('gamma',gamma)
 vals=[]
 for a in np.linspace(0,.999,6):
  J,Jc,delta,f=measures(gamma,a);g=J[0,1]-Jc[0,1];vals.append(g);print('bias',round(a,3),'pair-diff',round(g,8),'triple',round(delta,8),'f',round(f,6))
 if vals[0]*vals[-1]<0:
  root=brentq(lambda a:measures(gamma,a)[0][0,1]-measures(gamma,a)[1][0,1],0,.999,xtol=1e-13)
  J,Jc,delta,f=measures(gamma,root)
  assert np.max(np.abs(J-Jc))<1e-12
  assert np.max(np.abs(J-J[np.ix_([2,1,0],[2,1,0])].T))<1e-12
  assert 0<f<0.5 and delta>0
  Jr,_,delta_reversed,fr=measures(gamma,-root)
  assert np.max(np.abs(J-Jr))<1e-12 and abs(delta+delta_reversed)<1e-12 and abs(f-fr)<1e-12
  print('ROOT',root,'max_pair_difference',np.max(np.abs(J-Jc)),'triple',delta,'switch',f,'sigma_per_sample',gamma*root*np.log((1+root)/(1-root)))
 else:
  raise AssertionError(f'No matching-point sign change for gamma={gamma}')
