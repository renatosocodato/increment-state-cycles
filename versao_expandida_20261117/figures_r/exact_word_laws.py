"""Finite exact hidden-phase word laws; no Monte Carlo and no biological data."""

if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import csv, math
here=Path(__file__).resolve().parent
alphabet='EPR'; eps={'E':'R','P':'P','R':'E'}; w='EPRERP'
def rev(word): return ''.join(eps[x] for x in word[::-1])
def prob(word, eta):
    out=Q(0)
    for i in range(6):
        q=Q(1)
        for k,x in enumerate(word): q*=eta/3 + (1-eta)*int(x==w[(i+k)%6])
        out+=q/6
    return out
def allwords(m): return [''.join(t) for t in product(alphabet,repeat=m)]
def kl(m,eta):
    ps={x:prob(x,eta) for x in allwords(m)}
    return sum(float(p)*math.log(float(p/ps[rev(x)])) for x,p in ps.items() if p>0)
for eta in [Q(0),Q(1,10),Q(1,2),Q(1)]:
    for m in [1,2]:
        assert all(prob(x,eta)==prob(rev(x),eta) for x in allwords(m))
    assert prob('PRE',eta)-prob('REP',eta)==(1-eta)**2*(3-2*eta)/18
assert all(prob(x,Q(1,10))>0 for x in allwords(3))
with (here/'noise_exact.csv').open('w',newline='') as f:
    z=csv.DictWriter(f,fieldnames=['eta','pre','rep','delta','lag2','D1','D2','D3']);z.writeheader()
    for k in range(1,101):
        e=Q(k,100);z.writerow({'eta':float(e),'pre':float(prob('PRE',e)),'rep':float(prob('REP',e)), 'delta':float(prob('PRE',e)-prob('REP',e)),'lag2':float((1-e)**2/6),'D1':kl(1,e),'D2':kl(2,e),'D3':kl(3,e)})
with (here/'words_eta025.csv').open('w',newline='') as f:
    z=csv.DictWriter(f,fieldnames=['word','reverse','p','prev','difference']);z.writeheader()
    for x in allwords(3):
        p=prob(x,Q(1,4));pr=prob(rev(x),Q(1,4));z.writerow({'word':x,'reverse':rev(x),'p':float(p),'prev':float(pr),'difference':float(p-pr)})
with (here/'pairs_eta025.csv').open('w',newline='') as f:
    z=csv.DictWriter(f,fieldnames=['i','j','p']);z.writeheader()
    for a,b in product(alphabet,repeat=2):z.writerow({'i':a,'j':b,'p':float(prob(a+b,Q(1,4)))})
print('Exact: pair reversal symmetry, full support, and delta=(1-eta)^2(3-2eta)/18 verified.')
