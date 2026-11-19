# Changelog

## v1.1.0

- Added a Python API and an `increment-state-cycles-compare` CLI for independent and paired experimental designs.
- Added unit-level estimates, pointwise bootstrap intervals, and sensitivity grids for pause thresholds and sampling intervals.
- Added a synthetic CSV example, end-to-end tests, and a benchmark with known null and positive effects.

## v1.0.0

- Added an installable Python API and CSV command for physical reversal and empirical E/P/R contrasts.
- Added a single command for reproducing all five article figures in R in an isolated directory.
- Added API and CLI tests, an example dataset and version-specific software citation.

The source and saved results for the article are preserved from the commit cited in the EPJ E proof.

## 2026-11-18 — verification improvements

- The regeneration checker now deletes each expected output before invoking its producer and compares the rotor parameter JSON as well as the CSV tables. Its per-job timeout can be set for slower systems.
- Summary verifiers require the complete set of unique conditions and reconstruct the saved estimates, intervals and figure inputs where their source observations were retained. The rotor checker independently reconstructs all nine pair probabilities and the PRE/REP contrast from its rates and marker.
- Negative controls verify that no-output generators, missing summaries, a corrupted pair matrix and modified summary or plotting values are rejected.
- Figure 1 checks its displayed matrices against the defining parent transitions. Figure 2 rejects materially negative block divergences while allowing numerical round-off at zero.
- Categorical sampling now checks row normalization and sets the final cumulative probability to one; Wilson endpoints are constrained to [0,1] against floating-point round-off. The supplied numerical outputs remain unchanged within the declared comparison tolerances.
- Added a table dictionary and the physical simulation design file, and added the three rotor derivation checks to `run_checks.py`.

No saved numerical table, manuscript figure, scientific model, random seed or parameter was changed by this maintenance pass.


## 18 November 2026 — file-integrity check

Added a portable SHA-256 verification command and a negative control for a changed Figure 2 input table. This checks distributed file identity separately from the selective scientific checks; model results and figures were not changed.


## 18 November 2026 — safeguards for verification

Reject optimized Python in scripts that rely on assertions, validate finite rotor study values and their count lattice, and strengthen negative-control baselines and expected failure diagnostics. Published numerical results and figures are unchanged.
