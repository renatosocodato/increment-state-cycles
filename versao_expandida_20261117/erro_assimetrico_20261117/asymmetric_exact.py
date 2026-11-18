#!/usr/bin/env python3

if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from pathlib import Path
import sys,csv
import sympy as s
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'extensao_misturante_20261117'))
from mixing_exact import build,word
ROOT=Path(__file__).resolve().parent

def channel(B,a,b):
    return {'E':[(1-a)*e+b*r for e,r in zip(B['E'],B['R'])],
            'P':B['P'],'R':[a*e+(1-b)*r for e,r in zip(B['E'],B['R'])]}

def expressions(control):
    rho,eta,a,b=s.symbols('rho eta alpha beta',nonnegative=True)
    T,B,n=build(rho,eta,control,symbolic=True);B=channel(B,a,b)
    W=lambda w:word(w,T,B,n,True)
    return (rho,eta,a,b),{'marginal':s.factor(W('E')-W('R')),'q1':s.factor(W('EE')-W('RR')),'q2':s.factor(W('EP')-W('PR')),'triple':s.factor(W('PRE')-W('REP')),'lag2':s.factor(sum(W('P'+x+'E')-W('R'+x+'P') for x in 'EPR'))}

def main():
    expr={};params=None
    for name,ctrl in [('control',True),('directed',False)]:
        params,ex=expressions(ctrl);expr[name]=ex
        print(name,flush=True)
        for k,v in ex.items():print(k,':',v,flush=True)
    rho,eta,a,b=params
    assert s.simplify(expr['control']['marginal']-2*(b-a)/3)==0
    assert all(s.simplify(x.subs(b,a))==0 for x in expr['control'].values())
    assert s.simplify(expr['directed']['triple'].subs({a:0,b:0})-(1-rho)**2*(1-eta)**2*(3-2*eta)/18)==0
    assert s.simplify(expr['directed']['lag2'].subs({a:0,b:0})-(1-rho)**2*(1-eta)**2/6)==0
    rows=[]
    for r in [.2,.65]:
      for di in range(-80,81):
        delta=di/500;alpha=.08+delta/2;beta=.08-delta/2
        for model in expr:
          row={'rho':r,'eta':.25,'delta':delta,'alpha':alpha,'beta':beta,'model':model}
          row.update({k:float(v.subs({rho:r,eta:.25,a:alpha,b:beta})) for k,v in expr[model].items()});rows.append(row)
    with (ROOT/'exact_curves.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    print('Verified parity-symmetric channel null and no-additional-error baselines.')
if __name__=='__main__':main()
