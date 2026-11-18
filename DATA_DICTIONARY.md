# Numerical-output guide

All tables in this repository are generated from theoretical models. They contain no animal, cell, image or experimental measurements. Probabilities, contrasts and fractions are dimensionless. Time is measured in discrete observations or windows unless a script explicitly states otherwise.

## Tables and their roles

| Relative location | File | Contents / use |
| --- | --- | --- |
| `versao_expandida_20261117/figures_r/` | `noise_exact.csv` | Exact probabilities and divergences as symbol replacement varies; rendered as exploratory plots. |
| same | `pairs_eta025.csv` | Adjacent-pair probabilities at replacement probability 0.25. |
| same | `words_eta025.csv` | Three-symbol probabilities and their physically reversed partners at replacement probability 0.25. |
| `versao_expandida_20261117/extensao_misturante_20261117/` | `mixing_curves.csv` | Model-specific pair, triple, lag-two and block-divergence curves; Figure 2. |
| `versao_expandida_20261117/recuperacao_finita_20261117/` | `trajectories.csv` | One row per independently simulated trajectory, condition and repetition. |
| same | `summary.csv` | Summaries and model-specific threshold exceedance for each trajectory length and contrast. |
| `versao_expandida_20261117/erro_assimetrico_20261117/` | `exact_curves.csv` | Exact contrasts after the direct E/R swap channel; Figure 3. |
| same | `pause_exact_curves.csv` | Exact contrast for the alternative channel mapping E/R to P. |
| same | `finite_trajectories.csv` | One row per synthetic trajectory and asymmetry condition. |
| same | `finite_summary.csv` | Corresponding finite-trajectory means and exceedance fractions. |
| `versao_expandida_20261117/calibracao_independente_20261117/` | `studies.csv` | Point estimates and intervals for independent synthetic calibration studies. |
| same | `summary.csv` | Coverage, exclusion and interval-width summaries by method and calibration size. |
| same | `plot_estimates.csv` | Aggregated estimates and uncertainty used by Figure 4. |
| `recuperacao_fisica_20261118/` | `estudos_independentes.csv` | One row per synthetic rotor/control study and window length. |
| same | `resumo_recuperacao.csv` | Means, repetition intervals and exceedance fractions for Figure 5. |
| same | `parametros_e_verificacoes.json` | Seeds, model rates, matched pair matrix and exact contrast used by Figure 5. |

## Column meanings

- `E`, `P`, `R` denote positive, zero and negative increments; `word` is a sequence, `reverse` its order-reversed E/R-exchanged sequence. `i`, `j` are current and next symbols. `p` is a joint probability, `prev` the probability of the reversed word, and `difference` their difference.
- `rho` or `reset` is the phase-reset probability; `eta` is the original uniform-replacement probability; `alpha` and `beta` are the E-to-R and R-to-E error probabilities, and `delta=alpha-beta`. In `noise_exact.csv`, `delta` instead denotes a word-probability difference; consult that file's generating script.
- `q1` is P(EE)−P(RR), `q2` is P(EP)−P(PR), `marginal` is P(E)−P(R), `triple` or `delta3` is P(PRE)−P(REP), and `lag2` is P(S_t=P,S_(t+2)=E)−P(S_t=R,S_(t+2)=P). `pre` and `rep` are the two separate word probabilities.
- `diag` and `offdiag` are representative diagonal and off-diagonal entries of the matched pair law. `D1`, `D2`, `D3` and `kl3` are finite-block Kullback–Leibler divergences in nats; they are not thermodynamic rates.
- `model`, `arm` and `group` identify the specified synthetic generator, control or evaluation group. `replicate` and `study` index synthetic independent units; they are not biological replicates. `n` is a trajectory length, a number of independent studies or a valid-interval count according to the table; `ncal` is independent reference labels per class. `windows_per_trajectory` counts overlapping four-position windows; `trajectories_per_study` and `studies` count independent simulated units.
- `truth` and `expected` are known model values; `raw`, `point`, and `oracle_point` are uncorrected, estimated-channel-corrected, and known-channel-corrected estimates. `mean`, `median`, `sd`, `q025` and `q975` are summaries over independently generated units. `repeat_lo` and `repeat_hi` are the central repetition interval across studies.
- `threshold` is a model-specific empirical calibration cutoff; `exceed`, `rate`, `exceedance_fraction` and `nonzero` are corresponding observed fractions, and `k` or `exceedances` are counts. `lo`, `hi`, `exceed_lo`, `exceed_hi`, `wilson_low` and `wilson_high` are interval limits in the context specified by their table. They are not interchangeable: `plot_estimates.csv` uses intervals for across-study mean estimates; finite-exceedance tables use Wilson intervals conditional on the calibrated cutoff.
- `method` identifies a calibration uncertainty procedure (`fixed`, `joint`, or `oracle`); `fixed_lo/hi`, `joint_lo/hi` and `oracle_lo/hi` are its interval bounds. `coverage` is the empirical coverage fraction; `coverage_lo/hi` its Wilson limits. `abstain` counts intervals not reported; `mean_width` averages interval width; `min_sv` is the smallest estimated-channel singular value; `zero_cells` and `zero_cal_fraction` describe empty calibration cells; `boot_valid` and `mean_boot_valid` describe the fraction of invertible bootstrap matrices.

A script and parameter specification remains the authoritative definition where the same column label is used in more than one table.
