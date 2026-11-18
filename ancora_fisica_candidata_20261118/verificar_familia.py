import sympy as s
from itertools import product
b,d=s.symbols('b d',positive=True); t=b+d; h=[0,1,1,0,1,0]; Q=s.zeros(6)
for i in range(6):Q[i,i]=1-t;Q[i,(i+1)%6]=b;Q[i,(i-1)%6]=d
f=2*t/3;W=s.Matrix([[1-f,f],[f,1-f]])
def mats(Q,x):
 n=len(x); D={z:s.zeros(n) for z in 'EPR'}
 for i in range(n):
  for j in range(n):
   k=x[j]-x[i]; D['E' if k>0 else 'R' if k<0 else 'P'][i,j]=Q[i,j]
 return D
def p(D,w):
 n=D['E'].rows;v=s.ones(1,n)/n
 for a in w:v=v*D[a]
 return s.factor((v*s.ones(n,1))[0])
A=mats(Q,h);B=mats(W,[0,1])
for w in map(''.join,product('EPR',repeat=2)): print(w,'Jdriven=',p(A,w),'difference=',s.factor(p(A,w)-p(B,w)))
print('delta=',s.factor(p(A,'PRE')-p(A,'REP')))
