# Reproducibility package changes

## 2026-11-18 — verification improvements

- The regeneration checker now deletes each expected output before invoking its producer and compares the rotor parameter JSON as well as the CSV tables. Its per-job timeout can be set for slower systems.
- Summary verifiers require the complete set of unique conditions and reconstruct the saved estimates, intervals and figure inputs where their source observations were retained. The rotor checker independently reconstructs all nine pair probabilities and the PRE/REP contrast from its rates and marker.
- Negative controls verify that no-output generators, missing summaries, a corrupted pair matrix and modified summary or plotting values are rejected.
- Figure 1 checks its displayed matrices against the defining parent transitions. Figure 2 rejects materially negative block divergences while allowing numerical round-off at zero.
- Categorical sampling now checks row normalization and sets the final cumulative probability to one; Wilson endpoints are constrained to [0,1] against floating-point round-off. The supplied numerical outputs remain unchanged within the declared comparison tolerances.
- Added a table dictionary and the physical simulation design file, and added the three rotor derivation checks to `run_checks.py`.

No saved numerical table, manuscript figure, scientific model, random seed or parameter was changed by this maintenance pass.
