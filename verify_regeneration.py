#!/usr/bin/env python3
"""Regenerate numeric outputs in a temporary copy and compare saved tables."""

if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from pathlib import Path
import json, math, os, shutil, subprocess, sys, tempfile
import pandas as pd
import numpy as np
root=Path(__file__).resolve().parent
jobs=[
 ('versao_expandida_20261117/figures_r/exact_word_laws.py',['noise_exact.csv','pairs_eta025.csv','words_eta025.csv']),
 ('versao_expandida_20261117/extensao_misturante_20261117/mixing_exact.py',['mixing_curves.csv']),
 ('versao_expandida_20261117/recuperacao_finita_20261117/finite_recovery.py',['summary.csv','trajectories.csv']),
 ('versao_expandida_20261117/erro_assimetrico_20261117/asymmetric_exact.py',['exact_curves.csv']),
 ('versao_expandida_20261117/erro_assimetrico_20261117/exploratory_pause.py',['pause_exact_curves.csv']),
 ('versao_expandida_20261117/erro_assimetrico_20261117/finite_error.py',['finite_summary.csv','finite_trajectories.csv']),
 ('versao_expandida_20261117/calibracao_independente_20261117/synthetic_calibration.py',['studies.csv','summary.csv']),
 ('versao_expandida_20261117/calibracao_independente_20261117/prepare_plot.py',['plot_estimates.csv']),
 ('recuperacao_fisica_20261118/estudo_fisico.py',['estudos_independentes.csv','resumo_recuperacao.csv','parametros_e_verificacoes.json'])]
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',VECLIB_MAXIMUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
timeout=int(os.environ.get('EPJE_JOB_TIMEOUT_SECONDS','300'))
if timeout<=0: raise ValueError('EPJE_JOB_TIMEOUT_SECONDS must be a positive number of seconds')
def compare(p,q):
 if p.suffix == '.json':
  def same(a,b):
   if isinstance(a,bool) or isinstance(b,bool): return type(a) is type(b) and a==b
   if isinstance(a,int) or isinstance(b,int): return type(a) is int and type(b) is int and a == b
   if isinstance(a,float) and isinstance(b,float): return math.isclose(a,b,rel_tol=1e-10,abs_tol=1e-12)
   if isinstance(a,dict) and isinstance(b,dict): return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
   if isinstance(a,list) and isinstance(b,list): return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
   return type(a) is type(b) and a==b
  return same(json.loads(p.read_text()),json.loads(q.read_text()))
 a,b=pd.read_csv(p),pd.read_csv(q)
 if a.shape!=b.shape or list(a.columns)!=list(b.columns):return False
 for col in a.columns:
  if pd.api.types.is_numeric_dtype(a[col]) and pd.api.types.is_numeric_dtype(b[col]):
   if not np.allclose(a[col],b[col],rtol=1e-10,atol=1e-12,equal_nan=True):return False
  elif not a[col].fillna('<NA>').equals(b[col].fillna('<NA>')):return False
 return True
with tempfile.TemporaryDirectory(prefix='epje_reproduce_') as tmp:
 target=Path(tmp)/'repro'
 shutil.copytree(root,target,ignore=shutil.ignore_patterns('.git','.lake','__pycache__','*.pdf','*.png','*.svg','*.eps'))
 for script,files in jobs:
  print('Running',script,flush=True)
  # Remove only this job's expected outputs: preserved inputs and results from
  # earlier jobs remain available, but stale files cannot give a false pass.
  for fn in files:
   output=target/Path(script).parent/fn
   if output.exists(): output.unlink()
  try: subprocess.run([sys.executable,str(target/script)],cwd=target,env=env,timeout=timeout,check=True,stdout=subprocess.DEVNULL)
  except subprocess.TimeoutExpired:
   print('TIMEOUT:',script,flush=True);raise
  for fn in files:
   original=root/Path(script).parent/fn;new=target/Path(script).parent/fn
   ok=original.is_file() and new.is_file() and compare(original,new)
   print(' ',fn,'matches:',ok,flush=True)
   if not ok: raise RuntimeError('Output differs: '+str(original))
 print('All regenerated numeric outputs match the supplied tables and parameters within tolerance.',flush=True)
