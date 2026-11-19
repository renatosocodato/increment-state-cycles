#!/usr/bin/env python3
"""Render the five paper figures from the supplied tables in an isolated copy."""

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
EXPANDED = Path("versao_expandida_20261117")
RENDERERS = (
    (EXPANDED / "figures_r/render_physics_figures.R", "Figure_1"),
    (EXPANDED / "extensao_misturante_20261117/render_mixing.R", "Figure_mixing"),
    (EXPANDED / "erro_assimetrico_20261117/render_error.R", "Figure_asymmetric_error"),
    (EXPANDED / "calibracao_independente_20261117/render_calibration.R", "Figure_calibration"),
    (Path("recuperacao_fisica_20261118/figura_fisica.R"), "Figure_physical"),
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="New directory for the five PDFs and SVGs")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        parser.error("Use a new output directory.")
    if not shutil.which("Rscript"):
        parser.error("Rscript must be available on PATH.")
    try:
        with tempfile.TemporaryDirectory(prefix="increment-state-figures-") as work:
            workdir = Path(work)
            stage = workdir / "figures"
            stage.mkdir()
            for index, (script, stem) in enumerate(RENDERERS, 1):
                source = workdir / script.parent
                shutil.copytree(ROOT / script.parent, source, ignore=shutil.ignore_patterns(
                    "*.pdf", "*.svg", "*.eps", "*.png", "__pycache__"
                ))
                subprocess.run(["Rscript", "--vanilla", str(workdir / script)],
                               cwd=workdir, check=True, timeout=120)
                for suffix in (".pdf", ".svg"):
                    shutil.copy2(source / (stem + suffix), stage / f"Figure_{index}{suffix}")
            output.mkdir(parents=True)
            for path in stage.iterdir():
                shutil.copy2(path, output / path.name)
    except (OSError, subprocess.SubprocessError) as exc:
        parser.exit(1, f"Figure rendering failed: {exc}\n")


if __name__ == "__main__":
    main()
