#!/usr/bin/env python3
"""Build the package and audit every theorem in the boundary/shadow extension.

This targeted report does not replace the full historical endpoint audit in
verify.py. It checks upstream hashes, dependency revisions, all new source
modules, and the transitive axiom footprint of every new theorem.
"""
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("collatz_verify", ROOT / "scripts" / "verify.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
MODULES = ["ValuationRecurrence", "BoundaryLinearization", "ShadowOscillation",
           "ShadowGrowth", "ShadowRigidity", "ShadowLattice"]
OUT = ROOT / "verification"


def now():
    return datetime.now(timezone.utc).isoformat()


def run(args, log):
    with (OUT / log).open("w") as stream:
        result = subprocess.run(args, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {args}; see {log}")
    return (OUT / log).read_text()


def main():
    OUT.mkdir(exist_ok=True)
    report = {"status": "in_progress", "started_utc": now(),
              "scope": "Full package build and all new boundary/shadow theorem endpoints; historical endpoint audits are not rerun."}
    destination = OUT / "shadow-report.json"
    destination.write_text(json.dumps(report, indent=2) + "\n")
    try:
        manifest = json.loads((base.VENDOR / "source-manifest.json").read_text())
        for entry in manifest["source_files"]:
            path = (base.VENDOR / entry["path"]).resolve()
            assert path.is_relative_to(base.VENDOR.resolve()), "Upstream path escapes vendor"
            assert base.digest(path) == entry["sha256"], f"Upstream source changed: {path}"
        report["upstream_sources_checked"] = len(manifest["source_files"])
        locked = json.loads((base.VENDOR / "lake-manifest.json").read_text())["packages"]
        revisions = {}
        for package in locked:
            checkout = base.VENDOR / ".lake" / "packages" / package["name"]
            revision = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
            assert revision == package["rev"], f"Dependency revision changed: {package['name']}"
            revisions[package["name"]] = revision
        report["dependency_revisions"] = revisions
        sources = [ROOT / "CollatzTargetDensity" / f"{module}.lean" for module in MODULES]
        endpoints = []
        for module, path in zip(MODULES, sources):
            code = base.without_comments(path.read_text())
            assert not base.ESCAPES.search(code), f"Proof escape in {path}"
            endpoints.extend(f"CollatzTargetDensity.{module}.{name}" for name in
                             re.findall(r"^theorem\s+(\w+)", code, re.MULTILINE))
        audit = ROOT / "Verification" / "ShadowRigidity.lean"
        listed = re.findall(r"^#print axioms (\S+)", audit.read_text(), re.MULTILINE)
        assert len(listed) == len(set(listed)), "Duplicate audit endpoint"
        assert set(listed) == set(endpoints), "Audit does not cover precisely all new theorems"
        assert set(endpoints) <= set(base.REQUIRED), "Full verifier is missing new endpoints"
        hashed = sources + [audit, ROOT / "CollatzTargetDensity.lean", ROOT / "scripts" / "verify.py",
                            Path(__file__).resolve()]
        report["source_sha256"] = {str(p.relative_to(ROOT)): base.digest(p) for p in hashed}
        report["lean_toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        print("Source and dependency checks passed; building package.", flush=True)
        run(["lake", "build", "+CollatzTargetDensity:olean"], "shadow-package-build.log")
        print("Package build passed; auditing transitive axioms.", flush=True)
        evidence = run(["lake", "env", "lean", "Verification/ShadowRigidity.lean"],
                       "shadow-rigidity-axioms.log")
        footprints = {}
        for name in endpoints:
            pattern = "'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]"
            match = re.search(pattern, evidence, re.DOTALL)
            if match:
                axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
            elif f"'{name}' does not depend on any axioms" in evidence:
                axioms = set()
            else:
                raise RuntimeError(f"Missing axiom evidence: {name}")
            assert axioms <= base.ALLOWED, f"Unexpected axioms: {name}: {axioms - base.ALLOWED}"
            footprints[name] = sorted(axioms)
        for path in hashed:
            assert base.digest(path) == report["source_sha256"][str(path.relative_to(ROOT))], "Source changed during verification"
        report.update(status="verified", theorem_count=len(endpoints), axioms=footprints,
                      finished_utc=now())
    except Exception as error:
        report.update(status="failed", error=str(error), finished_utc=now())
        destination.write_text(json.dumps(report, indent=2) + "\n")
        raise
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified {len(endpoints)} theorem endpoints; see {destination}.", flush=True)


if __name__ == "__main__":
    main()
