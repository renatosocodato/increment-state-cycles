#!/usr/bin/env python3
"""Exercise specific failure modes against a known-good, temporary copy."""

if not __debug__:
    raise SystemExit('Python optimization disables required checks; run without -O or PYTHONOPTIMIZE.')
from pathlib import Path
import ast
import csv
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
           VECLIB_MAXIMUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')

def execute(target, program, *, extra_env=None, options=()):
    return subprocess.run([sys.executable, *options, str(target / program)], cwd=target,
                          env=dict(env, **(extra_env or {})), stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, timeout=60)

def accepted(target, program):
    result = execute(target, program)
    if result.returncode != 0:
        raise AssertionError(f'Baseline {program} failed:\n{result.stdout}')

def rejected(target, program, label, expected, *, extra_env=None, options=()):
    result = execute(target, program, extra_env=extra_env, options=options)
    if result.returncode == 0 or any(text not in result.stdout for text in expected):
        raise AssertionError(f'{label}: expected rejection {expected}, got:\n{result.stdout}')
    print('PASS:', label, 'was rejected for the expected reason')

with tempfile.TemporaryDirectory(prefix='epje_negative_') as temp:
    t = Path(temp) / 'repo'
    shutil.copytree(root, t, ignore=shutil.ignore_patterns('.git', '__pycache__', '*.pdf', '*.png', '*.svg', '*.eps'))
    accepted(t, 'run_checks.py')
    generator = t / 'versao_expandida_20261117/figures_r/exact_word_laws.py'
    original = generator.read_text(); generator.write_text('pass\n')
    rejected(t, 'verify_regeneration.py', 'nonproducing generator', ('Output differs:', 'noise_exact.csv'))
    generator.write_text(original)
    for name, script in (
        ('versao_expandida_20261117/recuperacao_finita_20261117/summary.csv', 'verify_recovery.py'),
        ('versao_expandida_20261117/erro_assimetrico_20261117/finite_summary.csv', 'verify_error.py'),
        ('versao_expandida_20261117/calibracao_independente_20261117/summary.csv', 'verify_calibration.py')):
        p = t / name; original = p.read_text(); p.write_text(original.splitlines()[0] + '\n')
        rejected(t, 'run_checks.py', 'empty ' + name, (script, 'AssertionError')); p.write_text(original)
    p = t / 'recuperacao_fisica_20261118/parametros_e_verificacoes.json'
    original = p.read_text(); m = json.loads(original); m['pair_matrix'] = [[0.0]*3 for _ in range(3)]; p.write_text(json.dumps(m))
    rejected(t, 'run_checks.py', 'zeroed Figure 5 pair matrix', ('verify_physical_saved.py', 'AssertionError')); p.write_text(original)
    for name, column, script in (
        ('versao_expandida_20261117/recuperacao_finita_20261117/summary.csv', 'sd', 'verify_recovery.py'),
        ('versao_expandida_20261117/erro_assimetrico_20261117/finite_summary.csv', 'hi', 'verify_error.py'),
        ('versao_expandida_20261117/calibracao_independente_20261117/plot_estimates.csv', 'mean', 'verify_calibration.py')):
        p = t / name; original = p.read_text()
        with p.open(newline='') as source: rows = list(csv.DictReader(source)); names = rows[0].keys()
        rows[0][column] = str(float(rows[0][column]) + 0.1)
        with p.open('w', newline='') as dest:
            w = csv.DictWriter(dest, fieldnames=names); w.writeheader(); w.writerows(rows)
        rejected(t, 'run_checks.py', 'altered ' + column + ' in ' + name, (script, 'AssertionError')); p.write_text(original)
    p = t / 'recuperacao_fisica_20261118/estudos_independentes.csv'
    original = p.read_text()
    with p.open(newline='') as source: rows = list(csv.DictReader(source)); names = rows[0].keys()
    row = next(row for row in rows if row['windows_per_trajectory'] == '256' and row['group'] == 'calibration_control')
    row['contrast'] = 'inf'
    with p.open('w', newline='') as dest:
        w = csv.DictWriter(dest, fieldnames=names); w.writeheader(); w.writerows(rows)
    rejected(t, 'run_checks.py', 'infinite rotor calibration contrast', ('verify_physical_saved.py', 'Rotor contrasts must be finite'))
    p.write_text(original)
    row['contrast'] = '0.00000001'
    with p.open('w', newline='') as dest:
        w = csv.DictWriter(dest, fieldnames=names); w.writeheader(); w.writerows(rows)
    rejected(t, 'run_checks.py', 'off-lattice rotor contrast', ('verify_physical_saved.py', 'integer window counts'))
    p.write_text(original)
    for p in sorted(t.rglob('*.py')):
        tree = ast.parse(p.read_text())
        requires_assertions = any(isinstance(node, ast.Assert) for node in ast.walk(tree))
        if requires_assertions or p.name in {'run_checks.py', 'verify_regeneration.py', 'test_checks.py'}:
            rejected(t, p.relative_to(t), 'optimized Python for ' + str(p.relative_to(t)),
                     ('Python optimization disables required checks',), options=('-O',))
    rejected(t, 'run_checks.py', 'PYTHONOPTIMIZE=1', ('Python optimization disables required checks',),
             extra_env={'PYTHONOPTIMIZE': '1'})
    tree = ast.parse((t / 'verify_regeneration.py').read_text())
    func = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'compare')
    scope = {'json': json, 'math': math}
    exec(compile(ast.Module(body=[func], type_ignores=[]), 'verify_regeneration.py', 'exec'), scope)
    a, b = Path(temp) / 'a.json', Path(temp) / 'b.json'
    a.write_text(json.dumps({'seed': 2026111803, 'rate': .5}))
    b.write_text(json.dumps({'seed': 2026111803.1, 'rate': .5}))
    if scope['compare'](a, b): raise AssertionError('fractional seed accepted')
    b.write_text(json.dumps({'seed': 2026111803, 'rate': .5 + 1e-12}))
    if not scope['compare'](a, b): raise AssertionError('valid floating point tolerance rejected')
    print('PASS: exact integer JSON comparison and floating tolerance')

with tempfile.TemporaryDirectory(prefix='epje_integrity_') as temp:
    t = Path(temp) / 'repo'; shutil.copytree(root, t, ignore=shutil.ignore_patterns('.git', '__pycache__'))
    accepted(t, 'verify_integrity.py')
    p = t / 'versao_expandida_20261117/extensao_misturante_20261117/mixing_curves.csv'
    p.write_bytes(p.read_bytes() + b'\n')
    rejected(t, 'verify_integrity.py', 'altered Figure 2 input table', ('Checksum mismatch:', 'mixing_curves.csv'))
print('All negative controls passed.')
