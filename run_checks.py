#!/usr/bin/env python3
"""Read-only checks on saved synthetic results and exact pair examples."""
from pathlib import Path
import os
import subprocess
import sys
root=Path(__file__).resolve().parent
scripts=['verificar_prova.py','contraste_margens_iguais_20261117.py','versao_expandida_20261117/recuperacao_finita_20261117/verify_recovery.py','versao_expandida_20261117/erro_assimetrico_20261117/verify_error.py','versao_expandida_20261117/calibracao_independente_20261117/verify_calibration.py','verify_physical_saved.py']
env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
for script in scripts:
 print('\n--',script,flush=True)
 subprocess.run([sys.executable,str(root/script)],cwd=root,env=env,check=True)
print('\nAll saved-data checks passed.')
