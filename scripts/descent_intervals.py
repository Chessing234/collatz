#!/usr/bin/env python3
"""Exact first-descent intervals and reproducible Lean certificates.

Python discovers candidates. Only ordinary Lean kernel-checked proofs certify
infinite classes. The census is finite and makes no universal coverage claim.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "Collatz/Research/DescentIntervals"
REPORT = ROOT / "Research/DescentIntervals"
BASELINE = "ca585a9b42633d89aaee7ba93be2c7cb105feb4b"
BATCH_COUNT = 100
CENSUS_DEPTH = 9


@dataclass(frozen=True)
class Interval:
    lower: int
    upper: int | None

    def contains(self, index: int) -> bool:
        return self.lower <= index and (self.upper is None or index < self.upper)

    def intersect(self, other: Interval) -> Interval:
        finite = [u for u in (self.upper, other.upper) if u is not None]
        return Interval(max(self.lower, other.lower), min(finite) if finite else None)

    @property
    def kind(self) -> str:
        if self.upper is None:
            return "tail"
        return "empty" if self.lower >= self.upper else "finite"


def require_naturals(*values: int) -> None:
    if any(type(value) is not int or value < 0 for value in values):
        raise ValueError("expected natural-number inputs")


def solve_le(a: int, b: int, c: int, d: int) -> Interval:
    """All m >= 0 satisfying a*m+b <= c*m+d, with no floating point."""
    require_naturals(a, b, c, d)
    if a <= c:
        if b <= d:
            return Interval(0, None)
        if a == c:
            return Interval(0, 0)
        return Interval((b - d - 1) // (c - a) + 1, None)
    if b <= d:
        return Interval(0, (d - b) // (a - c) + 1)
    return Interval(0, 0)


def trace(n: int, depth: int) -> tuple[list[int], list[int]]:
    require_naturals(n, depth)
    states, counts = [n], [0]
    for _ in range(depth):
        odd = n % 2
        n = (3 * n + 1) // 2 if odd else n // 2
        states.append(n)
        counts.append(counts[-1] + odd)
    return states, counts


def exact_interval(depth: int, residue: int) -> Interval:
    require_naturals(depth, residue)
    if depth == 0:
        return Interval(0, 0)
    states, counts = trace(residue, depth)
    modulus = 1 << depth
    result = solve_le(3 ** counts[-1], states[-1] + 1, modulus, residue)
    for j in range(depth):
        slope = 3 ** counts[j] * (1 << (depth - j))
        result = result.intersect(solve_le(modulus, residue, slope, states[j]))
    return result


def cutoff(t: int, scale: int, digit: int) -> int:
    require_naturals(t, scale, digit)
    if scale == 0:
        raise ValueError("refinement scale must be positive")
    return 0 if t <= digit else (t - digit - 1) // scale + 1


def pullback(interval: Interval, scale: int, digit: int) -> Interval:
    return Interval(cutoff(interval.lower, scale, digit),
                    None if interval.upper is None else cutoff(interval.upper, scale, digit))


def census(depth: int = CENSUS_DEPTH) -> list[dict]:
    rows = []
    for k in range(1, depth + 1):
        for r in range(1 << k):
            states, counts = trace(r, k)
            result = exact_interval(k, r)
            rows.append({"depth": k, "residue": r, "odd_count": counts[-1],
                         "endpoint": states[-1], **asdict(result), "kind": result.kind})
    return rows


def row_source(row: dict) -> str:
    k, r, a, b = (row[key] for key in ("depth", "residue", "odd_count", "endpoint"))
    lo, hi = row["lower"], row["upper"]
    upper = "none" if hi is None else f"some {hi}"
    membership = f"{lo} ≤ m" if hi is None else f"{lo} ≤ m ∧ m < {hi}"
    return f'''/-- Complete interval computation for depth {k}, residue {r}. -/
theorem bounds_{k}_{r} : exactInterval {k} {r} = ⟨{lo}, {upper}⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_{k}_{r} (m : Nat) :
    stoppingTime (2 ^ {k} * m + {r}) {k} ↔ {membership} := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_{k}_{r} m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_{k}_{r} : oddCount {r} {k} = {a} ∧ acceleratedOrbit {k} {r} = {b} := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_{k}_{r} (m : Nat) :
    acceleratedOrbit {k} (2 ^ {k} * m + {r}) = 3 ^ {a} * m + {b} := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_{k}_{r}.1, data_{k}_{r}.2]

'''


def generated_files() -> tuple[dict[Path, str], dict]:
    rows = census()
    files = {}
    batches = []
    for index in range(BATCH_COUNT):
        start = len(rows) * index // BATCH_COUNT
        stop = len(rows) * (index + 1) // BATCH_COUNT
        name = f"Batch{index + 1:03}"
        text = ("import Collatz.Research.DescentIntervals.Classifier\n\n"
                f"namespace Collatz.Research.DescentIntervals.{name}\n\n")
        text += "".join(row_source(row) for row in rows[start:stop])
        text += f"end Collatz.Research.DescentIntervals.{name}\n"
        path = LEAN / f"{name}.lean"
        files[path] = text
        batches.append({"module": name, "start": start, "stop": stop,
                        "sha256": hashlib.sha256(text.encode()).hexdigest()})
    imports = "".join(f"import Collatz.Research.DescentIntervals.{b['module']}\n" for b in batches)
    files[LEAN / "All.lean"] = (imports + "import Collatz.Research.DescentIntervals.Refinement\n"
                                "import Collatz.Research.DescentIntervals.Universal\n"
                                "import Collatz.Research.DescentIntervals.Cycles\n"
                                "import Collatz.Research.DescentIntervals.Examples\n")
    manifest = {"baseline": BASELINE, "census_depth": CENSUS_DEPTH,
                "batch_count": BATCH_COUNT, "cylinder_count": len(rows),
                "generated_theorem_count": 4 * len(rows), "batches": batches, "rows": rows}
    return files, manifest


def write_or_check(check: bool) -> dict:
    files, manifest = generated_files()
    files[REPORT / "manifest.json"] = json.dumps(manifest, indent=2) + "\n"
    for path, text in files.items():
        if check:
            if not path.is_file() or path.read_text() != text:
                raise RuntimeError(f"generated output mismatch: {path.relative_to(ROOT)}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    print(f"{'Checked' if check else 'Generated'} {manifest['cylinder_count']} cylinders in {BATCH_COUNT} batches", flush=True)
    return manifest


def commit_batches(manifest: dict) -> None:
    """Commit each batch only after Lake accepts it. Never stage other files."""
    for batch in manifest["batches"]:
        name = batch["module"]
        path = LEAN / f"{name}.lean"
        relative = str(path.relative_to(ROOT))
        result = subprocess.run(["lake", "build", f"Collatz.Research.DescentIntervals.{name}"],
                                cwd=ROOT, capture_output=True, text=True)
        (REPORT / f"{name}.build.log").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f"Lean rejected {name}; see its build log")
        tracked = subprocess.run(["git", "ls-files", "--error-unmatch", relative],
                                 cwd=ROOT, capture_output=True).returncode == 0
        if tracked:
            clean = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", relative], cwd=ROOT)
            if clean.returncode == 0:
                print(f"Already committed and rechecked {name}", flush=True)
                continue
        subprocess.run(["git", "add", "--", relative], cwd=ROOT, check=True)
        first = manifest["rows"][batch["start"]]
        last = manifest["rows"][batch["stop"] - 1]
        message = (f"proof: classify descent intervals {name} "
                   f"({first['depth']}:{first['residue']} through {last['depth']}:{last['residue']})")
        subprocess.run(["git", "commit", "--only", "-m", message, "--", relative], cwd=ROOT, check=True,
                       stdout=subprocess.DEVNULL)
        print(f"Checked and committed {name}: {batch['stop'] - batch['start']} infinite classes", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify deterministic generated files without writing")
    parser.add_argument("--commit", action="store_true", help="build and commit each certificate batch")
    args = parser.parse_args()
    manifest = write_or_check(args.check)
    if args.commit:
        commit_batches(manifest)


if __name__ == "__main__":
    main()
