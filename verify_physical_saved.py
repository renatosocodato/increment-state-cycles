#!/usr/bin/env python3
"""Reconstruct stationary rotor word laws and check their finite-study summaries."""
from itertools import product
from pathlib import Path
import json
import numpy as np
import pandas as pd
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parent / 'recuperacao_fisica_20261118'
MARKER = np.array([0, 1, 1, 0, 1, 0])
WINDOWS = (256, 1024, 4096)
ARMS = ('test_control', 'test_driven', 'test_reversed_drive')


def word_laws(transition, marker):
    increments = marker[None, :] - marker[:, None]
    kernels = {s: transition * (increments == k) for s, k in zip('EPR', (1, 0, -1))}

    def probability(word):
        row = np.full(len(marker), 1 / len(marker))
        for symbol in word:
            row = row @ kernels[symbol]
        return row.sum()

    pairs = np.array([[probability(a + b) for b in 'EPR'] for a in 'EPR'])
    return pairs, probability('PRE'), probability('REP')


def check(actual, expected):
    np.testing.assert_allclose(actual, expected, rtol=0, atol=1e-12)


def reconstruct(meta):
    plus, minus = meta['rates_per_sample']
    assert plus > minus > 0
    check(plus + minus, 1)
    check(meta['bias'], (plus - minus) / (plus + minus))
    identity = np.eye(len(MARKER))
    generator = (plus * np.roll(identity, 1, axis=1)
                 + minus * np.roll(identity, -1, axis=1) - (plus + minus) * identity)
    transition = expm(generator)
    flip = np.sum(transition * (MARKER[:, None] != MARKER[None, :])) / len(MARKER)
    check(meta['control_flip_per_sample'], flip)
    control = np.array([[1 - flip, flip], [flip, 1 - flip]])
    pairs, pre, rep = word_laws(transition, MARKER)
    reverse_pairs, rev_pre, rev_rep = word_laws(transition.T, MARKER)
    null_pairs, null_pre, null_rep = word_laws(control, np.array([0, 1]))
    check(meta['pair_matrix'], pairs)
    check(pairs, reverse_pairs)
    check(pairs, null_pairs)
    check(meta['max_pair_mismatch'], np.max(np.abs(pairs - null_pairs)))
    check([meta['driven_PRE'], meta['driven_REP']], [pre, rep])
    contrasts = (null_pre - null_rep, pre - rep, rev_pre - rev_rep)
    check(contrasts[0], 0)
    check(contrasts[2], -contrasts[1])
    assert contrasts[1] > 0
    for key, value in zip(('equilibrium', 'driven', 'opposite'), contrasts):
        check(meta['expected_contrasts'][key], value)
    return dict(zip(ARMS, contrasts))


def main():
    raw = pd.read_csv(ROOT / 'estudos_independentes.csv', float_precision='round_trip')
    summary = pd.read_csv(ROOT / 'resumo_recuperacao.csv', float_precision='round_trip')
    meta = json.loads((ROOT / 'parametros_e_verificacoes.json').read_text())
    assert meta['seed'] == 2026111803 and meta['windows_per_trajectory'] == list(WINDOWS)
    assert meta['calibration_studies_per_length'] == meta['test_studies_per_model_and_length'] == 600
    assert meta['lengths_are_nested'] is True and meta['independent_trajectories_per_study'] == 24
    truth = reconstruct(meta)
    assert len(raw) == 3 * 4 * 600
    assert set(zip(raw.windows_per_trajectory, raw.group, raw.study)) == set(
        product(WINDOWS, ('calibration_control', *ARMS), range(600)))
    assert len(summary) == 9
    assert set(zip(summary.windows_per_trajectory, summary.model)) == set(product(WINDOWS, ARMS))
    for n in WINDOWS:
        group = raw[raw.windows_per_trajectory == n]
        calibration = group[group.group == 'calibration_control'].contrast.to_numpy()
        threshold = np.quantile(np.abs(calibration), .95, method='higher')
        for arm in ARMS:
            x = group[group.group == arm].contrast.to_numpy()
            row = summary[(summary.windows_per_trajectory == n) & (summary.model == arm)].iloc[0]
            check([row.threshold, row['mean'], row['median'], row.expected],
                  [threshold, x.mean(), np.median(x), truth[arm]])
            check([row.repeat_lo, row.repeat_hi], np.quantile(x, [.025, .975]))
            hits = np.count_nonzero(np.abs(x) > threshold)
            assert row.exceedances == hits and row.studies == 600 and row.trajectories_per_study == 24
            rate = hits / 600
            z = 1.959963984540054
            center = (rate + z*z / 1200) / (1 + z*z / 600)
            radius = z * np.sqrt(rate * (1-rate) / 600 + (z / 1200)**2) / (1 + z*z / 600)
            check([row.exceedance_fraction, row.wilson_low, row.wilson_high],
                  [rate, max(0, center-radius), min(1, center+radius)])
    print('Rotor pair laws, PRE and REP, calibration thresholds and all finite-study summaries verified.')


if __name__ == '__main__':
    main()
