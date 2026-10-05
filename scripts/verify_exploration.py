"""Build and audit every declaration in the isolated Collatz exploration.

This verifier covers only Collatz/Exploration and its named audits. It does not
certify unrelated pre-existing research or the entire repository. All theorem
and definition names are enumerated from these source files, then queried by
Lean itself for their transitive axiom dependencies. Only Lean's ordinary
logical axioms are accepted. Build success alone is not an integrity check.
"""
from __future__ import annotations

import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "Collatz" / "Exploration"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z0-9_]+)",
    re.MULTILINE,
)
AUDITS = {
    "HalvingBlocks": "audit_halving_blocks.lean",
    "OrbitFloor": "audit_orbit_floor.lean",
    "TimeChange": "audit_time_change.lean",
    "FirstDescent": "audit_first_descent.lean",
    "ResiduePotential": "audit_residue_potential.lean",
    "RankReduction": "audit_rank_reduction.lean",
    "RankGrowth": "audit_rank_growth.lean",
    "RankTransport": "audit_rank_transport.lean",
    "AdaptiveResidueObstruction": "audit_adaptive_residue.lean",
    "BlockRanking": "audit_block_ranking.lean",
    "DensityBoundary": "audit_density_boundary.lean",
    "TraceCertificate": "audit_trace_certificate.lean",
    "ThreePowerLift": "audit_three_power_lift.lean",
    "ThreeUnitLift": "audit_three_unit_lift.lean",
    "ThreePowerUnits": "audit_three_power_units.lean",
    "AffinePowerMatch": "audit_affine_power_match.lean",
    "DyadicConvergentClasses": "audit_dyadic_convergent_classes.lean",
    "ExponentSearch": "audit_exponent_search.lean",
    "ExponentRaise": "audit_exponent_raise.lean",
    "ComputedClassWitness": "audit_computed_class_witness.lean",
}


def run(command: list[str]) -> str:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    if result.returncode:
        raise RuntimeError(f"Command failed: {' '.join(command)}\n{output}")
    if re.search(r"\b(?:sorryAx|Lean\.ofReduceBool)\b", output):
        raise RuntimeError(f"Unaccepted proof dependency:\n{output}")
    return output


def main() -> None:
    files = sorted(DIRECTORY.glob("*.lean"))
    if not files:
        raise RuntimeError("Exploration source directory is empty")
    unknown = {path.stem for path in files} - set(AUDITS)
    if unknown:
        raise RuntimeError(f"Add concrete audit coverage for new modules: {unknown}")
    modules = ["Collatz.Exploration." + path.stem for path in files]
    declarations: list[str] = []
    for path, module in zip(files, modules):
        source = path.read_text()
        # All files in this isolated exploration deliberately avoid these
        # tokens, including comments, so a simple source rejection is adequate.
        if re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", source):
            raise RuntimeError(f"Forbidden source token: {path}")
        for name in DECLARATION.findall(source):
            declarations.append(module + "." + name)
    if not declarations:
        raise RuntimeError("No declarations enumerated")
    umbrella = ROOT / "Collatz" / "Exploration.lean"
    imports = set(re.findall(r"^import (Collatz\.Exploration\.[A-Za-z0-9_]+)$",
                             umbrella.read_text(), re.MULTILINE))
    if imports != set(modules):
        raise RuntimeError("Exploration entry point does not import exactly the audited modules")
    run(["lake", "build", "Collatz.Exploration"])
    for path in files:
        run(["lake", "env", "lean", "scripts/" + AUDITS[path.stem]])
    queries = "\n".join("import " + module for module in modules) + "\n"
    queries += "\n".join("#print axioms " + name for name in declarations) + "\n"
    with tempfile.TemporaryDirectory(prefix="collatz-exploration-audit-") as folder:
        audit = Path(folder) / "AllDeclarations.lean"
        audit.write_text(queries)
        output = run(["lake", "env", "lean", str(audit)])
    found: set[str] = set()
    for name, dependencies in re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL
    ):
        axioms = {value.strip() for value in dependencies.split(",") if value.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axioms for {name}: {axioms - ALLOWED_AXIOMS}")
        found.add(name)
    found.update(re.findall(r"'([^']+)' does not depend on any axioms", output))
    missing = set(declarations) - found
    if missing:
        raise RuntimeError(f"Lean did not return an axiom report for: {missing}")
    run(["python3", "scripts/probe_residue_potential.py"])
    run(["python3", "scripts/probe_dyadic_convergent_classes.py"])
    print(json.dumps({
        "status": "passed",
        "modules": len(modules),
        "declarations_audited": len(declarations),
        "concrete_audits": len(files),
        "accepted_axioms": sorted(ALLOWED_AXIOMS),
        "scope": "Collatz/Exploration only",
    }, indent=2))


if __name__ == "__main__":
    main()
