import sympy as s
from itertools import product
h=[0,1,1,0,1,0]
t=s.Rational(1,2); b=t*(1+1/s.sqrt(3))/2; d=t*(1-1/s.sqrt(3))/2
Q=s.zeros(6)
for i in range(6):
 Q[i,i]=1-t; Q[i,(i+1)%6]=b; Q[i,(i-1)%6]=d
W=s.Matrix([[s.Rational(2,3),s.Rational(1,3)],[s.Rational(1,3),s.Rational(2,3)]])
def matrices(Q,x):
 n=len(x); D={c:s.zeros(n) for c in 'EPR'}
 for i in range(n):
  for j in range(n):
   sign=x[j]-x[i]; sym='E' if sign>0 else 'R' if sign<0 else 'P';D[sym][i,j]=Q[i,j]
 return D
def prob(D,word):
 n=D['E'].rows; row=s.ones(1,n)/n
 for z in word:row=row*D[z]
 return s.simplify((row*s.ones(n,1))[0])
A=matrices(Q,h);B=matrices(W,[0,1]); eps={'E':'R','P':'P','R':'E'}
def reverse(w):return ''.join(eps[c] for c in w[::-1])
for w in map(''.join,product('EPR',repeat=2)):
 x=prob(A,w);y=prob(B,w);assert s.simplify(x-y)==0 and s.simplify(x-prob(A,reverse(w)))==0
 print(w, x)
for w in map(''.join,product('EPR',repeat=3)):
 assert s.simplify(prob(B,w)-prob(B,reverse(w)))==0
print('delta3',s.simplify(prob(A,'PRE')-prob(A,'REP')))
print('formula',s.simplify((b**3-d**3)/6))
print('difference',s.simplify(prob(A,'PRE')-prob(A,'REP')-(b**3-d**3)/6))
print('params',b,d,'P+ P-',s.simplify(prob(A,'PRE')),s.simplify(prob(A,'REP')))
