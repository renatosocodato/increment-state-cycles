# Matched observation support and the genotype × phase contrast in radial q1

This exploratory application compares the within-animal change (After minus Before) between CKO and control. q1 is the probability of two consecutive outward increments minus the probability of two consecutive inward increments in projected tip-to-soma distance. Each animal contributes equally within its genotype.

The closest equal windows have 59 nominal observations each, frames 1–59 and 60–118, spanning 58 minutes within each window. The pause grid is 0, 0.10, 0.25, 0.50, 1 and 2 in archived coordinate units. Sampling is at 1, 2 and 4 nominal minutes, anchored to the first nominal frame of each phase window. Observations are never joined across a missing frame or across phases. The matching key is animal, cell and protrusion ID from tracking. It does not independently establish identity across injury in the films.

| Analysis at 0.10 and 1 min | Control / CKO | Mean change control | Mean change CKO | Interaction (CKO minus control), 95% pointwise interval |
| --- | --- | ---: | ---: | --- |
| Equal nominal windows, all observed traces | 7 / 7 | +0.271 | +0.175 | −0.096 [−0.228, +0.043] |
| Equal nominal windows, same animals as the matched traces | 4 / 5 | +0.284 | +0.160 | −0.124 [−0.300, +0.054] |
| Same eligible protrusion IDs, all valid frames in each phase | 4 / 5 | +0.066 | +0.149 | +0.083 [−0.216, +0.408] |
| Same tracked protrusions and same relative frame support | 4 / 5 | −0.102 | +0.052 | +0.154 [−0.148, +0.526] |

Within each sampling setting, the ID-only analysis uses exactly the protrusion IDs retained by strict frame matching. It keeps all valid frames within each phase for those IDs and still breaks at gaps. At 1 minute both restrictions use the same 27 IDs and the same nine animals. The step from all traces in those nine animals to the same IDs shifts the interaction by +0.207 (paired-by-animal bootstrap 95% interval [−0.058, +0.591]). Requiring the same relative frame slots then shifts it by +0.071 [−0.154, +0.256]. These are changes in the estimate when changing the analysis population and support, with no causal interpretation. The ID restriction shifted the interaction upward at all 18 settings and the slot restriction at 17/18. Both the ID-only and the strict interaction estimates were negative in only 1/18 settings.

The intervals are percentile intervals from 5,000 bootstrap draws of animals within genotype, preserving within-animal phase differences and, for the two steps, the paired analysis modes. They are pointwise and describe a small cohort. At 4 minutes the strict comparison retains 23 protrusion IDs. Differences in baseline behavior, persistence and trackability remain live explanations. The comparison cannot establish a genotype effect on lesion response.

## Reproduce

Provide the original Feather archive directory containing `xy_frame_features.feather` and `xy_raw_long.feather`. The script checks tip and soma coordinates against the source and applies the documented rule that excludes whole animal-frames with conflicting source coordinates. It uses Increment State Cycles 1.1.0 plus NumPy, pandas and PyArrow.

```sh
python analisar.py /path/to/cohort1_intravital/feather --output results --aggregate-only
```

`interacao.csv`, `contagens.csv` and `efeitos_das_restricoes.csv` contain only aggregate estimates and counts. Omit `--aggregate-only` when working locally to save individual changes and the source audit. The manuscript and software release are independent of this exploratory application.

## Visual review of the phase boundary

All 27 target IDs were linked to nine deposited movie files and visually inspected with tip and soma overlays in frames 58–61 around the documented transition. Tracking has coordinates on both sides of the boundary for all 27 IDs. The overlays used the TIFF pixel calibration for image display, which placed the soma markers on the expected cell bodies. Several terminal processes were faint or were close enough to neighboring tips that unique identity remained unresolved. The review therefore supports field and soma correspondence and flags ambiguities at the branch level. It is a targeted review of boundary frames, not an independent retracking of the full sequences. The reported contrasts retain the original tracking assignments and do not selectively exclude ambiguous targets.

The [complete-sequence visual sensitivity](visual_sensitivity/#masked-review-of-complete-tracked-sequences) quantifies how the exploratory interaction changes after a conservative exclusion of ambiguous tracks and shows the change due to animal eligibility separately.
