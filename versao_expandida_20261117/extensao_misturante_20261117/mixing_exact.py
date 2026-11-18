
if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from itertools import product
from pathlib import Path
import csv
import numpy as np
import sympy as s
S='EPR'; eps={'E':'R','P':'P','R':'E'}; cycle='EPRERP'
reverse=''.join(eps[x] for x in cycle[::-1]); root=Path(__file__).resolve().parent

def build(r,e,control=False,symbolic=False):
    cycles=[cycle,reverse] if control else [cycle]; n=6*len(cycles)
    T=s.zeros(n) if symbolic else np.zeros((n,n)); one=s.Integer(1) if symbolic else 1.0
    for i in range(n):
        for j in range(n): T[i,j]=r/n+(one-r if j//6==i//6 and j%6==(i%6+1)%6 else 0)
    B={x:[(one-e if c==x else 0)+e/3 for cyc in cycles for c in cyc] for x in S}
    return T,B,n

def word(w,T,B,n,symbolic=False):
    if symbolic:
        v=s.Matrix([[s.Rational(1,n)*q for q in B[w[0]]]])
        for x in w[1:]: v=(v*T)*s.diag(*B[x])
        return s.factor(sum(v))
    v=np.array(B[w[0]])/n
    for x in w[1:]: v=(v@T)*np.array(B[x])
    return float(v.sum())

def rev(w): return ''.join(eps[x] for x in w[::-1])
def tests():
    r,e=s.symbols('r eta', nonnegative=True);t,b,n=build(r,e,symbolic=True);tc,bc,nc=build(r,e,True,True)
    W=lambda z:word(z,t,b,n,True); C=lambda z:word(z,tc,bc,nc,True)
    for w in map(''.join,product(S,repeat=2)):
        assert s.simplify(W(w)-W(rev(w)))==0 and s.simplify(W(w)-C(w))==0
    for w in map(''.join,product(S,repeat=3)):
        assert s.simplify(C(w)-C(rev(w)))==0
        assert s.simplify(W(w)-W(w[::-1]))==0
    # Reflection k -> -k conjugates the single-cycle transition to its transpose.
    for i in range(6):
        for j in range(6): assert s.simplify(t[i,j]-t[(-j)%6,(-i)%6])==0
    assert all(cycle[(-i)%6]==cycle[i] for i in range(6))
    # In the indexed reverse cycle used here, theta swaps cycles and k -> 5-k.
    theta=lambda i: (1-i//6)*6+(5-i%6)
    for i in range(12):
        assert reverse[(5-i%6)]==eps[cycle[i%6]] if i<6 else cycle[(5-i%6)]==eps[reverse[i%6]]
        for j in range(12): assert s.simplify(tc[i,j]-tc[theta(j),theta(i)])==0
    d=s.factor(W('PRE')-W('REP')); lag=s.factor(sum(W('P'+x+'E')-W('R'+x+'P') for x in S))
    assert s.simplify(d-(1-r)**2*(1-e)**2*(3-2*e)/18)==0
    assert s.simplify(lag-(1-r)**2*(1-e)**2/6)==0
    print('Symbolic pair laws and control triples verified; contrasts:',d,lag)
    for length in range(1,6):
        t,b,n=build(.23,.25,True)
        assert max(abs(word(w,t,b,n)-word(rev(w),t,b,n)) for w in map(''.join,product(S,repeat=length)))<1e-12
    print('Control reversal checked numerically through length five.')

def generate():
    rows=[]
    for r in np.linspace(0,1,101):
        e=.25
        for model in ['Directed','Reversible control']:
            t,b,n=build(r,e,model!='Directed'); W=lambda w:word(w,t,b,n)
            p={''.join(w):W(''.join(w)) for w in product(S,repeat=3)}
            kl=sum(v*np.log(v/p[rev(w)]) for w,v in p.items() if v>0)
            rows.append(dict(reset=r,eta=e,model=model,diag=W('EE'),offdiag=W('EP'),delta3=W('PRE')-W('REP'),lag2=sum(W('P'+x+'E')-W('R'+x+'P') for x in S),kl3=kl))
    with (root/'mixing_curves.csv').open('w',newline='') as f:
        wr=csv.DictWriter(f,fieldnames=rows[0].keys());wr.writeheader();wr.writerows(rows)
if __name__=='__main__': tests();generate()
