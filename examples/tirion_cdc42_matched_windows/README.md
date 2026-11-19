# Matched observation support and the genotype × phase contrast in radial q1

This exploratory application compares the within-animal change (After minus Before) between CKO and control. q1 is the probability of two consecutive outward increments minus the probability of two consecutive inward increments in projected tip-to-soma distance. Each animal contributes equally within its genotype.

The closest equal windows have 59 nominal observations each, frames 1–59 and 60–118, spanning 58 minutes within each window. The pause grid is 0, 0.10, 0.25, 0.50, 1 and 2 in archived coordinate units. Sampling is at 1, 2 and 4 nominal minutes, anchored to the first nominal frame of each phase window. Observations are never joined across a missing frame or across phases. The matching key is animal, cell and protrusion ID from tracking. It does not independently establish identity across injury in the films.

| Analysis at 0.10 and 1 min | Control / CKO | Mean change control | Mean change CKO | Interaction (CKO minus control), 95% pointwise interval |
| --- | --- | ---: | ---: | --- |
| Equal nominal windows, all observed traces | 7 / 7 | +0.271 | +0.175 | −0.096 [−0.228, +0.043] |
| Equal nominal windows, same animals as the matched traces | 4 / 5 | +0.284 | +0.160 | −0.124 [−0.300, +0.054] |
| Same tracked protrusions and same relative frame support | 4 / 5 | −0.102 | +0.052 | +0.154 [−0.148, +0.526] |

At 1 minute, the strict analysis contains 27 eligible protrusion IDs observed in both windows. At 4 minutes, 23 remain. Strict matching retains only relative frame slots with coordinates in both phases, splits on missing slots, and yields identical eligible window counts before and after within each animal. Estimates had negative signs in 16/18 settings with all observed traces, 15/18 with all traces in the matched animals and 1/18 with strict matching. Fixing membership within each analysis across the full grid yielded 17/18, 17/18 and 1/18 negative, respectively. At the nominal reference setting, omitting one animal at a time left the all-traces interactions negative, while the strict estimate could change sign.

This reversal persists when animal membership is held constant at the reference setting. The strict estimate describes the subset of trace IDs and frame slots observed on both sides of injury. That subset can differ in preexisting behavior, persistence or trackability. The contrast between analysis modes cannot identify the contribution of each source of selection or establish a genotype effect on lesion response. The intervals are percentile intervals from 5,000 bootstrap draws of animals within genotype, preserving within-animal phase differences. They are pointwise and describe a small cohort. Repeating the strict comparison with prospectively tracked IDs and matched frame coverage would discriminate a trace-composition explanation from a reproducible difference in within-trace dynamics.

## Reproduce

Provide the original Feather archive directory containing `xy_frame_features.feather` and `xy_raw_long.feather`. The script checks tip and soma coordinates against the source and applies the documented rule that excludes whole animal-frames with conflicting source coordinates. It uses Increment State Cycles 1.1.0 plus NumPy, pandas and PyArrow.

```sh
python analisar.py /path/to/cohort1_intravital/feather --output results --aggregate-only
```

`interacao.csv` and `contagens.csv` contain only aggregate estimates and counts. Omit `--aggregate-only` when working locally to save individual changes and the source audit. The manuscript and software release are independent of this exploratory application.
