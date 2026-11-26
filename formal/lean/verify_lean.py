"""Rebuild the formal companion and inspect every theorem's transitive axioms."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
NAMESPACES = {
    "IncrementCycles": "IncrementCycles",
    "RotorRational": "RotorRational",
    "RotorEnclosure": "RotorEnclosure",
    "ObservedReversal": "IncrementCycles.ObservedReversal",
    "ResetMixing": "IncrementCycles.ResetMixing",
    "RotorMatching": "RotorMatching",
    "RotorFourier": "RotorFourier",
    "RotorGenerator": "RotorGenerator",
    "CycleExpansion": "CycleExpansion",
    "StatementDomains": "StatementDomains",
    "StatementAlignment": "StatementAlignment",
}
MODULES = tuple(NAMESPACES)
STATEMENTS = "ManuscriptStatements.lean"
OUTPUT = HERE / "verification-output"
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}


def run(*args):
    result = subprocess.run(args, cwd=HERE, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, check=False, timeout=900)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    sources = {name: (HERE / f"{name}.lean").read_text() for name in MODULES}
    checked_sources = {**sources, STATEMENTS: (HERE / STATEMENTS).read_text()}
    for name, source in checked_sources.items():
        if re.search(r"\b(sorry|admit)\b|^\s*(axiom|unsafe)\b", source, re.M):
            raise ValueError(f"Proof placeholder or added axiom in {name}")
    declarations = [f"{NAMESPACES[name]}.{theorem}" for name, source in sources.items()
                    for theorem in re.findall(r"^(?:@\[[^\n]+\] )?(?:theorem|lemma) (\w+)", source, re.M)]
    build = run("lake", "build")
    statements = run("lake", "env", "lean", STATEMENTS)
    commands = [*(f"import {name}" for name in MODULES),
                *(f"#print axioms {name}" for name in declarations)]
    with tempfile.TemporaryDirectory(prefix="epje-lean-audit-") as temp:
        check = Path(temp) / "Axioms.lean"
        check.write_text("\n".join(commands) + "\n")
        output = run("lake", "env", "lean", str(check))
    OUTPUT.mkdir(exist_ok=True)
    (OUTPUT / "build.log").write_text(build)
    (OUTPUT / "statements.log").write_text(statements)
    (OUTPUT / "axioms.log").write_text(output)
    dependencies = {}
    for name, trailing in re.findall(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",
                                    output, re.M):
        brackets = re.search(r"\[([^\]]*)\]", trailing)
        dependencies[name] = sorted(value.strip() for value in brackets[1].split(",") if value.strip()) if brackets else []
    if set(declarations) != set(dependencies):
        raise ValueError(f"Missing audit output for {set(declarations) - set(dependencies)}")
    unexpected = set().union(*dependencies.values()) - ALLOWED
    if unexpected:
        raise ValueError(f"Unexpected transitive axioms: {sorted(unexpected)}")
    hashed = [*(f"{name}.lean" for name in MODULES), STATEMENTS, "lean-toolchain", "lakefile.toml", "lake-manifest.json"]
    report = {"lean": run("lake", "env", "lean", "--version").strip(),
              "theorems": len(dependencies),
              "transitive_axioms": sorted(set().union(*dependencies.values())),
              "sha256": {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in hashed},
              "dependencies": dependencies}
    (OUTPUT / "axioms.json").write_text(json.dumps(report, indent=2) + "\n")
    print(report["lean"])
    print("Manuscript statement types checked for Eqs. (2) and (4).")
    print(f"{len(dependencies)} theorems checked; axioms: {', '.join(report['transitive_axioms'])}")


if __name__ == "__main__":
    main()
