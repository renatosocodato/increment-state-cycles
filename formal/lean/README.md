# Lean 4 companion to Increment-state cycles do not determine physical reversibility

This Lake project contains the machine-checked results for the EPJ E manuscript. The tag [epje-lean-v1.0.0](https://github.com/renatosocodato/increment-state-cycles/releases/tag/epje-lean-v1.0.0) identifies the formalization. The manuscript cites [42a4d664](https://github.com/renatosocodato/increment-state-cycles/tree/42a4d6640adf6c3ab25fd41ca3432e10978652fb) for the computational reproduction and figures. The Lean project runs independently of the Python package and R figure pipeline.

## Run the checks

With [Elan](https://github.com/leanprover/elan) (on PATH), Git, and Python 3 installed, run from the repository root:

```sh
cd formal/lean
awk '/^import Mathlib\./ { print $2 }' ./*.lean | sort -u | xargs lake exe cache get
python3 verify_lean.py
python3 rotor_certificate.py
```

Elan uses the Lean version in `lean-toolchain`. Lake uses the Mathlib commit and transitive dependency revisions in `lake-manifest.json`. The cache command is for a fresh checkout and fetches compiled Mathlib imports. The first Python command builds all formal modules, checks the two manuscript statement types, and writes the theorem-by-theorem axiom report to `verification-output/axioms.json`. The release contains 197 named theorems and uses only `Classical.choice`, `Quot.sound`, and `propext` as transitive axioms. The second command independently evaluates selected rotor bounds with exact rational interval arithmetic.

## Results checked by Lean

| Manuscript | Formal result |
| --- | --- |
| Eqs. (1)–(2) | [IncrementCycles](IncrementCycles.lean) proves the E/R swap for physical reversal of a time-reversal-even coordinate, including symmetric threshold boundaries. It proves the pair criterion under stationarity. [ManuscriptStatements](ManuscriptStatements.lean) checks the type of Eq. (2) directly. |
| Eq. (3) and Fig. 1 | [IncrementCycles](IncrementCycles.lean) checks the two exact counterexamples. [StatementAlignment](StatementAlignment.lean) checks the log ratio on the domain of six positive factors. |
| Eq. (4) | [ManuscriptStatements](ManuscriptStatements.lean) checks the endpoint correction for any nonempty finite sequence, including a single symbol. |
| Eqs. (5)–(7), (10)–(11) | [CycleExpansion](CycleExpansion.lean) expands the hidden-state sums for the pair and triple probabilities and the lag-two marginal. [StatementAlignment](StatementAlignment.lean) connects these probabilities to strict triple separation for the directed cycle and a zero contrast for the control. |
| Eqs. (8)–(9) | [StatementDomains](StatementDomains.lean) checks the reversal of PRE to REP, the singular support at zero noise, and the one-sided divergence limit. |
| Control and reset mixing | [ObservedReversal](ObservedReversal.lean) checks physical reversal of observed words of every finite length for the control. [ResetMixing](ResetMixing.lean) checks stationarity and convergence for the hidden reset kernels. |
| Eqs. (12)–(13) | [IncrementCycles](IncrementCycles.lean) proves population-law inversion under a known invertible product channel. [StatementDomains](StatementDomains.lean) checks the inverse for the specified example matrix. |
| Eq. (14) and Fig. 5 | [RotorGenerator](RotorGenerator.lean) connects the sampled continuous-time generator to the Poisson series. [RotorFourier](RotorFourier.lean) and [RotorEnclosure](RotorEnclosure.lean) give the autocorrelation formula and rational bounds. [StatementAlignment](StatementAlignment.lean), in `figure5_checked`, proves existence of a common bias in [0.52363, 0.52365] where all nine observed pair probabilities agree and the triple-contrast gap exceeds 0.002436. |

The formal scope is the stated mathematical models and their assumptions. The manuscript uses the general data-processing inequality and infinite-process ergodicity arguments separately. The Monte Carlo studies are part of the computational reproduction.
