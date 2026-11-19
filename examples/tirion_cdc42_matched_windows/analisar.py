"""Compare q1 changes in equal intravital windows at the animal level."""
import argparse
import hashlib
from importlib.metadata import version
import json
from pathlib import Path

import numpy as np
import pandas as pd
from increment_state_cycles import contrasts
from increment_state_cycles.modulation import symbolise

THRESHOLDS = (0, 0.10, 0.25, 0.50, 1, 2)
STRIDES = (1, 2, 4)
GEO = ["prot_x", "prot_y", "soma_x", "soma_y"]
KEYS = ["mouse_id", "cell_id", "protrusion_id", "frame"]
RAW_KEYS = ["mouse_id", "cell_id", "frame", "entity"]


def load(root):
    files = [root / "xy_frame_features.feather", root / "xy_raw_long.feather"]
    d = pd.read_feather(files[0], columns=KEYS + GEO + ["genotype", "sex", "phase", "context"])
    raw = pd.read_feather(files[1]).rename(columns={"animal_id": "mouse_id", "cell_id": "full_cell_id", "sheet": "cell_id"})
    no_frame = int(d.frame.isna().sum())
    d = d.dropna(subset=["frame"]).copy()
    for table in (d, raw):
        table.mouse_id = table.mouse_id.str.lower()
        assert np.isfinite(table.frame).all() and (table.frame % 1 == 0).all()
        table.frame = table.frame.astype(int)
    assert ((d.frame < 60) == (d.phase == "Before")).all()
    assert ((d.context == "A_Baseline") == (d.phase == "Before")).all()
    raw.entity = raw.entity.str.lower().str.replace(r"\s+", "", regex=True)
    raw = raw.drop_duplicates(RAW_KEYS + ["x", "y"])
    conflicts = raw[raw.duplicated(RAW_KEYS, keep=False)][["mouse_id", "frame"]].drop_duplicates()
    rejected = pd.MultiIndex.from_frame(conflicts)
    raw = raw.loc[~pd.MultiIndex.from_frame(raw[["mouse_id", "frame"]]).isin(rejected)]
    d = d.loc[~pd.MultiIndex.from_frame(d[["mouse_id", "frame"]]).isin(rejected)].copy()
    assert not raw.duplicated(RAW_KEYS).any() and not d.duplicated(KEYS).any()
    checks = {}
    for entity, xy in (("tip", GEO[:2]), ("soma", GEO[2:])):
        e = d[KEYS + xy].copy()
        e["entity"] = "cellcenter" if entity == "soma" else e.protrusion_id.str.replace("prot_", "protrusion", regex=False)
        e = e.dropna(subset=xy)
        z = e.merge(raw[RAW_KEYS + ["x", "y"]], on=RAW_KEYS, how="left", validate="many_to_one", indicator=True)
        assert (z._merge == "both").all()
        error = np.abs(z[xy].to_numpy() - z[["x", "y"]].to_numpy())
        assert np.isfinite(error).all() and error.max() <= 1e-11
        checks[entity] = {"verified_rows": len(z), "max_abs_error": float(error.max())}
    finite = np.isfinite(d[GEO]).all(axis=1)
    d = d.loc[finite].copy()
    d["radius"] = np.hypot(d.prot_x - d.soma_x, d.prot_y - d.soma_y)
    audit = {"files_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
             "excluded_mouse_frames": conflicts.to_dict("records"),
             "feature_rows_without_frame_excluded": no_frame,
             "nonfinite_rows_excluded_after_conflict_removal": int((~finite).sum()),
             "source_coordinate_checks": checks, "eligible_position_rows": len(d)}
    return d, audit


SEED = 20261119
DRAWS = 5000
GRID = ["threshold", "stride_min"]


def estimates(data, cohort):
    rng = np.random.default_rng(SEED)
    draws = {}
    for setting, group in data.groupby(GRID, sort=True):
        groups = {name: group.loc[group.genotype.eq(name)].sort_values("animal")
                  for name in ("ctl", "cko")}
        ids = tuple(tuple(frame.animal) for frame in groups.values())
        ctl, cko = [frame.change.to_numpy(float) for frame in groups.values()]
        if min(len(ctl), len(cko)) < 2:
            raise ValueError(f"Too few animals at {setting}")
        if ids not in draws:
            draws[ids] = tuple(rng.integers(0, len(x), (DRAWS, len(x))) for x in (ctl, cko))
        i, j = draws[ids]
        boot = cko[j].mean(axis=1) - ctl[i].mean(axis=1)
        low, high = np.quantile(boot, [0.025, 0.975])
        ctl_loo = (ctl.sum() - ctl) / (len(ctl) - 1)
        cko_loo = (cko.sum() - cko) / (len(cko) - 1)
        loo = np.r_[cko.mean() - ctl_loo, cko_loo - ctl.mean()]
        yield dict(cohort=cohort, threshold=setting[0], stride_min=setting[1],
                   n_ctl=len(ctl), n_cko=len(cko), mean_change_ctl=ctl.mean(),
                   mean_change_cko=cko.mean(), interaction=cko.mean()-ctl.mean(),
                   ci_low=low, ci_high=high, loo_low=loo.min(), loo_high=loo.max())


# Closest non-overlapping windows around the documented boundary at frame 60.
# They contain 59 nominal observations and span 58 min from first to last.
WINDOW_START = {"Before": 1, "After": 60}
WINDOW_LENGTH = 59
TRACE = ["mouse_id", "genotype", "cell_id", "protrusion_id"]


def build_tracks(data, mode):
    groups = {"Before": {}, "After": {}}
    for key, group in data.groupby(TRACE + ["phase"], sort=True):
        *trace, phase = key
        start = WINDOW_START[phase]
        positions = group.loc[group.frame.between(start, start + WINDOW_LENGTH - 1)]
        if not positions.empty:
            groups[phase][tuple(trace)] = dict(zip(positions.frame - start, positions.radius))
    if mode == "same_support":
        shared_keys = groups["Before"].keys() & groups["After"].keys()
        matched = {"Before": {}, "After": {}}
        for trace in sorted(shared_keys):
            shared_slots = groups["Before"][trace].keys() & groups["After"][trace].keys()
            if shared_slots:
                for phase in matched:
                    matched[phase][trace] = {slot: groups[phase][trace][slot] for slot in shared_slots}
        groups = matched
    return groups


def windows(groups, mode, stride):
    """Anchor sampling to each window start; break at all original-frame gaps."""
    tracks = {}
    eligible_trace_keys = set()
    for phase, by_trace in groups.items():
        for trace, slots in by_trace.items():
            animal, genotype, _, _ = trace
            selected = np.array(sorted(slots), dtype=int)
            for contiguous in np.split(selected, np.flatnonzero(np.diff(selected) != 1) + 1):
                sampled = contiguous[contiguous % stride == 0]
                if len(sampled) >= 3:
                    tracks.setdefault((animal, genotype, phase), []).append(
                        tuple(slots[int(i)] for i in sampled))
                    eligible_trace_keys.add((phase, trace))
    if mode == "same_support":
        before = {t for p,t in eligible_trace_keys if p == "Before"}
        after = {t for p,t in eligible_trace_keys if p == "After"}
        assert before == after
    return tracks, eligible_trace_keys


def calculate(groups, mode):
    rows, counts = [], []
    for stride in STRIDES:
        traces, eligible_traces = windows(groups, mode, stride)
        for threshold in THRESHOLDS:
            metrics = {}
            for key, fragments in traces.items():
                seq = [symbolise(fragment, threshold) for fragment in fragments]
                stats = contrasts(seq)
                metrics[key] = (stats["q1"], stats["adjacent_windows"])
            for animal, genotype, phase in sorted(metrics):
                if phase != "Before" or (animal, genotype, "After") not in metrics:
                    continue
                before, n_before = metrics[animal, genotype, "Before"]
                after, n_after = metrics[animal, genotype, "After"]
                if mode == "same_support":
                    assert n_before == n_after
                rows.append(dict(mode=mode, threshold=threshold, stride_min=stride, animal=animal,
                                 genotype=genotype.lower(), before=before, after=after, change=after-before,
                                 before_windows=n_before, after_windows=n_after))
        counts.append(dict(mode=mode, stride_min=stride,
                           before_traces=sum(p == "Before" for p, _ in eligible_traces),
                           after_traces=sum(p == "After" for p, _ in eligible_traces)))
    return pd.DataFrame(rows), counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("feather_directory", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--aggregate-only", action="store_true", help="omit animal IDs and source audit")
    args = parser.parse_args()
    assert version("increment-state-cycles") == "1.1.0"
    data, audit = load(args.feather_directory)
    series, tables, counts = [], [], []
    for mode in ("equal_windows", "same_support"):
        animals, trace_counts = calculate(build_tracks(data, mode), mode)
        assert len(animals.groupby(GRID)) == len(THRESHOLDS) * len(STRIDES)
        series.append(animals)
        counts.extend(trace_counts)
    equal, same = series
    matched_animals = equal.merge(same[GRID + ["animal"]], on=GRID + ["animal"], validate="one_to_one")
    matched_animals["mode"] = "equal_windows_same_animals"
    series.append(matched_animals)
    for animals in series:
        mode = animals["mode"].iat[0]
        fixed = set.intersection(*(set(g.animal) for _,g in animals.groupby(GRID)))
        for cohort, subset in (("eligible_by_setting", animals),
                               ("fixed_across_grid", animals.loc[animals.animal.isin(fixed)])):
            tables.extend(dict(mode=mode, **row) for row in estimates(subset, cohort))
    args.output.mkdir(parents=True, exist_ok=True)
    pd.DataFrame(tables).to_csv(args.output / "interacao.csv", index=False)
    pd.DataFrame(counts).to_csv(args.output / "contagens.csv", index=False)
    if not args.aggregate_only:
        pd.concat(series, ignore_index=True).to_csv(args.output / "mudanca_por_animal.csv", index=False)
        (args.output / "origem.json").write_text(json.dumps(audit, indent=2) + "\n")


if __name__ == "__main__":
    main()
