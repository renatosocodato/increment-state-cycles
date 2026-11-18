#!/usr/bin/env python3
"""Synthetic independent classification calibration; frozen study design."""
from pathlib import Path
import csv,sys,math
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'recuperacao_finita_20261117'))
from finite_recovery import CYCLE,wilson
ROOT=Path(__file__).resolve().parent
C=np.array([[.86,.04,.10],[.03,.94,.03],[.03,.05,.92]])
N=3002; NREP=200; B=200; NS=(100,500,2000); BLOCK=30; RHO=.2; ETA=.25

def trajectories(model,rng):
 nphase=6 if model=='directed' else 12
 phase=rng.integers(0,nphase,size=NREP);out=np.empty((N,NREP),dtype=np.uint8)
 assert np.all(C>=0) and np.allclose(C.sum(axis=1),1,rtol=0,atol=1e-12)
 cc=C.cumsum(axis=1);cc[:,-1]=1.0
 for t in range(N):
  z=CYCLE[phase].copy();mask=rng.random(NREP)<ETA;z[mask]=rng.integers(0,3,size=mask.sum())
  out[t]=(rng.random(NREP)[:,None]>cc[z]).sum(axis=1)
  if t<N-1:
   reset=rng.random(NREP)<RHO;phase=(phase//6)*6+(phase%6+1)%6
   phase[reset]=rng.integers(0,nphase,size=reset.sum())
 return out

def block_counts(x):
 a=x[:-2].astype(int);b=x[1:-1].astype(int);c=x[2:].astype(int)
 ids=np.repeat(np.arange(100),BLOCK)
 tri=np.bincount(ids*27+a*9+b*3+c,minlength=2700).reshape(100,27)
 lag=np.bincount(ids*9+a*3+c,minlength=900).reshape(100,9)
 return tri,lag

def weights(inv):
 w=np.atleast_3d(inv) if inv.ndim==2 else inv
 if inv.ndim==2:w=inv[None,:,:]
 E,P,R=w[:,:,0],w[:,:,1],w[:,:,2]
 triple=(np.einsum('bi,bj,bk->bijk',P,R,E)-np.einsum('bi,bj,bk->bijk',R,E,P)).reshape(-1,27)
 lag=(np.einsum('bi,bj->bij',P,E)-np.einsum('bi,bj->bij',R,P)).reshape(-1,9)
 return triple,lag

def estimate(q3,q2,inv):
 v3,v2=weights(inv)
 return np.sum(q3*v3,axis=1),np.sum(q2*v2,axis=1)

def summarize_cal(n,rng):
 counts=np.vstack([rng.multinomial(n,row) for row in C]);return counts,counts/n

def run_study(x,ncal,rng,model,index):
 counts,chat=summarize_cal(ncal,rng)
 if np.linalg.svd(chat,compute_uv=False)[-1]<=.05: return []
 inv=np.linalg.inv(chat);tri,lag=block_counts(x)
 q3=tri.sum(axis=0,keepdims=True)/3000;q2=lag.sum(axis=0,keepdims=True)/3000
 raw=estimate(q3,q2,np.eye(3));point=estimate(q3,q2,inv);orpoint=estimate(q3,q2,np.linalg.inv(C))
 mult=rng.multinomial(100,np.full(100,.01),size=B)
 boot3=mult@tri/3000;boot2=mult@lag/3000
 fixed=estimate(boot3,boot2,inv);oracle=estimate(boot3,boot2,np.linalg.inv(C))
 bc=np.stack([rng.multinomial(ncal,chat[i],size=B)/ncal for i in range(3)],axis=1)
 valid=np.linalg.svd(bc,compute_uv=False)[:,-1]>.05
 joint=estimate(boot3[valid],boot2[valid],np.linalg.inv(bc[valid])) if valid.mean()>=.95 else None
 rows=[]
 for j,key in enumerate(['triple','lag2']):
  truth=(0 if model=='control' else (.05 if key=='triple' else .06))
  row=dict(model=model,ncal=ncal,study=index,contrast=key,truth=truth,raw=raw[j][0],point=point[j][0],oracle_point=orpoint[j][0],min_sv=np.linalg.svd(chat,compute_uv=False)[-1],zero_cells=int((counts==0).sum()),boot_valid=valid.mean())
  for label,arr in [('fixed',fixed[j]),('oracle',oracle[j]),('joint',None if joint is None else joint[j])]:
   lo,hi=(np.nan,np.nan) if arr is None else np.quantile(arr,[.025,.975]);row[label+'_lo']=lo;row[label+'_hi']=hi
  rows.append(row)
 return rows
def main():
 seeds=iter(np.random.SeedSequence(20261119).spawn(6*(NREP+1)))
 rows=[]
 for model in ['control','directed']:
  for ncal in NS:
   obs=trajectories(model,np.random.default_rng(next(seeds)))
   for i in range(NREP): rows.extend(run_study(obs[:,i],ncal,np.random.default_rng(next(seeds)),model,i))
   print('completed',model,ncal,'studies:',len(rows),flush=True)
 with (ROOT/'studies.csv').open('w',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
 summary=[]
 for model in ['control','directed']:
  for ncal in NS:
   for key in ['triple','lag2']:
    sub=[r for r in rows if r['model']==model and r['ncal']==ncal and r['contrast']==key]
    for method in ['fixed','joint','oracle']:
     valid=[r for r in sub if np.isfinite(r[method+'_lo'])]
     if not valid: continue
     covered=sum(r[method+'_lo']<=r['truth']<=r[method+'_hi'] for r in valid)
     positive=sum(r[method+'_lo']>0 or r[method+'_hi']<0 for r in valid)
     clo,chi=wilson(covered,len(valid));plo,phi=wilson(positive,len(valid))
     summary.append(dict(model=model,ncal=ncal,contrast=key,method=method,n=len(valid),abstain=NREP-len(valid),mean_point=np.mean([r['oracle_point'] if method=='oracle' else r['point'] for r in valid]),mean_raw=np.mean([r['raw'] for r in valid]),truth=valid[0]['truth'],coverage=covered/len(valid),coverage_lo=clo,coverage_hi=chi,nonzero=positive/len(valid),nonzero_lo=plo,nonzero_hi=phi,mean_width=np.mean([r[method+'_hi']-r[method+'_lo'] for r in valid]),zero_cal_fraction=np.mean([r['zero_cells']>0 for r in valid]),mean_boot_valid=np.mean([r['boot_valid'] for r in valid])))
 with (ROOT/'summary.csv').open('w',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=summary[0].keys());writer.writeheader();writer.writerows(summary)
 print('finished',flush=True)
if __name__=='__main__':main()
