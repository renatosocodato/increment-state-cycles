#!/usr/bin/env python3
"""Negative controls: corrupted inputs and a nonproducing generator must fail."""
from pathlib import Path
import csv
import json
import os
import shutil
import subprocess
import sys
import tempfile

root=Path(__file__).resolve().parent
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')

def rejected(target, program, label):
 p=subprocess.run([sys.executable,str(target/program)],cwd=target,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60)
 if p.returncode==0: raise AssertionError(f'{label}: corrupted input was accepted')
 print('PASS:',label,'was rejected')

with tempfile.TemporaryDirectory(prefix='epje_negative_') as temp:
 t=Path(temp)/'repo';shutil.copytree(root,t,ignore=shutil.ignore_patterns('.git','__pycache__','*.pdf','*.png','*.svg','*.eps'))
 generator=t/'versao_expandida_20261117/figures_r/exact_word_laws.py'
 original=generator.read_text();generator.write_text('pass\n')
 rejected(t,'verify_regeneration.py','generator that writes no outputs');generator.write_text(original)
 for name in ('versao_expandida_20261117/recuperacao_finita_20261117/summary.csv','versao_expandida_20261117/erro_assimetrico_20261117/finite_summary.csv','versao_expandida_20261117/calibracao_independente_20261117/summary.csv'):
  p=t/name;original=p.read_text();p.write_text(original.splitlines()[0]+'\n')
  rejected(t,'run_checks.py','empty '+name);p.write_text(original)
 p=t/'recuperacao_fisica_20261118/parametros_e_verificacoes.json'
 original=p.read_text();m=json.loads(original);m['pair_matrix']=[[0.0]*3 for _ in range(3)];p.write_text(json.dumps(m))
 rejected(t,'run_checks.py','zeroed Figure 5 pair matrix');p.write_text(original)
 for name,column in (('versao_expandida_20261117/recuperacao_finita_20261117/summary.csv','sd'),
                     ('versao_expandida_20261117/erro_assimetrico_20261117/finite_summary.csv','hi'),
                     ('versao_expandida_20261117/calibracao_independente_20261117/plot_estimates.csv','mean')):
  p=t/name;original=p.read_text()
  with p.open(newline='') as source: rows=list(csv.DictReader(source)); names=rows[0].keys()
  rows[0][column]=str(float(rows[0][column])+0.1)
  with p.open('w',newline='') as dest:
   w=csv.DictWriter(dest,fieldnames=names);w.writeheader();w.writerows(rows)
  rejected(t,'run_checks.py','altered '+column+' in '+name);p.write_text(original)
print('All negative controls passed.')
