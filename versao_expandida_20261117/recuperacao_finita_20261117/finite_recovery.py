#!/usr/bin/env python3
from pathlib import Path
import csv, math, sys
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'extensao_misturante_20261117'))
from mixing_exact import build, word
ROOT=Path(__file__).resolve().parent
RHO=(.20,.65); LENGTH=(100,300,1000,3000); ETA=.25; NREP=2000; SEED=20261117
CYCLE=np.array([0,1,2,0,2,1, 1,0,2,0,1,2],dtype=np.uint8)

def pair_kernel(rho):
    T,B,n=build(rho,ETA)
    return np.array([[3*word(a+b,T,B,n) for b in 'EPR'] for a in 'EPR'])

def simulate(model,n,rho,rng):
    if model=='markov':
        states=rng.integers(0,3,size=NREP);kernel=pair_kernel(rho)
        assert np.all(kernel>=0) and np.allclose(kernel.sum(axis=1),1,rtol=0,atol=1e-12)
        cum=np.cumsum(kernel,axis=1);cum[:,-1]=1.0
    else:
        nphase=6 if model=='directed' else 12
        states=rng.integers(0,nphase,size=NREP)
    x=np.empty((n,NREP),dtype=np.uint8)
    for t in range(n):
        if model=='markov':
            x[t]=states
            if t<n-1:
                u=rng.random(NREP);states=(u[:,None]>cum[states,:]).sum(axis=1)
        else:
            symbols=CYCLE[states].copy();noise=rng.random(NREP)<ETA
            symbols[noise]=rng.integers(0,3,size=noise.sum());x[t]=symbols
            if t<n-1:
                reset=rng.random(NREP)<rho;states=(states//6)*6+(states%6+1)%6
                states[reset]=rng.integers(0,nphase,size=reset.sum())
    a,b,c=x[:-2],x[1:-1],x[2:]
    triple=(((a==1)&(b==2)&(c==0)).sum(axis=0)-((a==2)&(b==0)&(c==1)).sum(axis=0))/(n-2)
    lag2=(((a==1)&(c==0)).sum(axis=0)-((a==2)&(c==1)).sum(axis=0))/(n-2)
    return triple,lag2

def wilson(k,n):
    z=1.959963984540054;p=k/n;d=1+z*z/n;center=(p+z*z/(2*n))/d
    half=z*math.sqrt(p*(1-p)/n+z*z/(4*n*n))/d
    return max(0.0,center-half),min(1.0,center+half)
def main():
    seedseq=np.random.SeedSequence(SEED);streams=iter(seedseq.spawn(len(RHO)*len(LENGTH)*4))
    summaries=[];samples=[]
    for rho in RHO:
        for n in LENGTH:
            calibration=simulate('control',n,rho,np.random.default_rng(next(streams)))
            thresholds=[float(np.quantile(np.abs(z),.95,method='higher')) for z in calibration]
            for arm in ['control','markov','directed']:
                result=simulate(arm,n,rho,np.random.default_rng(next(streams)))
                for i,key in enumerate(['triple','lag2']):
                    vals=result[i];k=int(np.sum(np.abs(vals)>thresholds[i]));lo,hi=wilson(k,NREP)
                    truth=0. if arm!='directed' else (1-rho)**2*(1-ETA)**2*((3-2*ETA)/18 if key=='triple' else 1/6)
                    q=np.quantile(vals,[.025,.5,.975])
                    summaries.append(dict(rho=rho,n=n,arm=arm,contrast=key,truth=truth,mean=vals.mean(),sd=vals.std(ddof=1),q025=q[0],median=q[1],q975=q[2],threshold=thresholds[i],exceed=k/NREP,exceed_lo=lo,exceed_hi=hi,k=k,replicates=NREP))
                for j,(x,y) in enumerate(zip(*result)):
                    samples.append(dict(rho=rho,n=n,arm=arm,replicate=j,triple=x,lag2=y))
            print(f'completed rho={rho}, n={n}',flush=True)
    for fn,rows in [('summary.csv',summaries),('trajectories.csv',samples)]:
        with (ROOT/fn).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
if __name__=='__main__': main()
