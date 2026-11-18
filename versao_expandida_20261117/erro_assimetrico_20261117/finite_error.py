#!/usr/bin/env python3
from pathlib import Path
import csv,sys
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'recuperacao_finita_20261117'))
from finite_recovery import CYCLE,wilson
ROOT=Path(__file__).resolve().parent
RHO=(.2,.65);LENGTH=(300,3000);DELTAS=(-.16,-.08,0,.08,.16);NR=2000;ETA=.25

def simulate(n,rho,delta,rng):
    alpha=.08+delta/2;beta=.08-delta/2
    phase=rng.integers(0,12,size=NR);x=np.empty((n,NR),dtype=np.uint8)
    for t in range(n):
        u=CYCLE[phase].copy();replace=rng.random(NR)<ETA
        u[replace]=rng.integers(0,3,size=replace.sum())
        flip=rng.random(NR);e=(u==0)&(flip<alpha);r=(u==2)&(flip<beta)
        u[e]=2;u[r]=0;x[t]=u
        if t<n-1:
            reset=rng.random(NR)<rho;phase=(phase//6)*6+(phase%6+1)%6
            phase[reset]=rng.integers(0,12,size=reset.sum())
    a,b,c=x[:-2],x[1:-1],x[2:]
    triple=(((a==1)&(b==2)&(c==0)).sum(axis=0)-((a==2)&(b==0)&(c==1)).sum(axis=0))/(n-2)
    lag2=(((a==1)&(c==0)).sum(axis=0)-((a==2)&(c==1)).sum(axis=0))/(n-2)
    return triple,lag2

def main():
    streams=iter(np.random.SeedSequence(20261118).spawn(len(RHO)*len(LENGTH)*(1+len(DELTAS))))
    summaries=[];samples=[]
    for rho in RHO:
      for n in LENGTH:
        cal=simulate(n,rho,0,np.random.default_rng(next(streams)))
        threshold=[float(np.quantile(abs(v),.95,method='higher')) for v in cal]
        for delta in DELTAS:
          vals=simulate(n,rho,delta,np.random.default_rng(next(streams)))
          for i,key in enumerate(['triple','lag2']):
            k=int(np.sum(abs(vals[i])>threshold[i]));lo,hi=wilson(k,NR)
            summaries.append(dict(rho=rho,n=n,delta=delta,contrast=key,mean=vals[i].mean(),sd=vals[i].std(ddof=1),threshold=threshold[i],rate=k/NR,lo=lo,hi=hi,k=k,replicates=NR))
          samples.extend(dict(rho=rho,n=n,delta=delta,replicate=i,triple=a,lag2=b) for i,(a,b) in enumerate(zip(*vals)))
        print(f'completed rho={rho} N={n}',flush=True)
    for filename,rows in [('finite_summary.csv',summaries),('finite_trajectories.csv',samples)]:
        with (ROOT/filename).open('w',newline='') as f:
            w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
if __name__=='__main__':main()
