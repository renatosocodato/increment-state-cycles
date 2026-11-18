import sys
from pathlib import Path
import sympy as s
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'extensao_misturante_20261117'))
from mixing_exact import build,word
rho,eta,a,b=s.symbols('rho eta alpha beta',nonnegative=True)
T,B,n=build(rho,eta,True,True)
B2={'E':[(1-a)*v for v in B['E']], 'R':[(1-b)*v for v in B['R']], 'P':[p+a*e+b*r for p,e,r in zip(B['P'],B['E'],B['R'])]}
W=lambda w:word(w,T,B2,n,True)
for key,val in [('marginal',W('E')-W('R')),('q1',W('EE')-W('RR')),('q2',W('EP')-W('PR')),('triple',W('PRE')-W('REP')),('lag2',sum(W('P'+x+'E')-W('R'+x+'P') for x in 'EPR'))]:
 print(key,':',s.factor(val))
import csv
expr=s.factor(W('PRE')-W('REP'))
rows=[]
for r in [.2,.65]:
 for di in range(-80,81):
  delta=di/500;alpha=.08+delta/2;beta=.08-delta/2
  rows.append(dict(rho=r,delta=delta,triple=float(expr.subs({rho:r,eta:.25,a:alpha,b:beta}))))
with (Path(__file__).resolve().parent/'pause_exact_curves.csv').open('w',newline='') as f:
 writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
