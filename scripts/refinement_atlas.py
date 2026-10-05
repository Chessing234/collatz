#!/usr/bin/env python3
"""Reproduce 900 sharp residue-refinement certificates; check before each commit.
No arbitrary source files are staged. No numerical assertion uses native_decide.
"""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'Collatz/Research/RefinementAtlas'


def orbit(n, k):
    a = 0
    for _ in range(k):
        a += n % 2
        n = (3 * n + 1) // 2 if n % 2 else n // 2
    return a, n


def run(args):
    p = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError(p.stdout + p.stderr)
    return p.stdout


def render_case(k, r, a, b, g, t):
    tag = f'{k}_{r}'
    A, C = 2**k, 3**a
    return f'''/-- Kernel-evaluated parity count and endpoint for ({k}, {r}). -/
theorem data_{tag} : oddCount {r} {k} = {a} ∧
    acceleratedOrbit {k} {r} = {b} := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_{tag} : gap {k} {r} = {g} ∧ {C} < {A} := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_{tag} : threshold {k} {r} = {t} := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_{tag} (m : Nat) :
    acceleratedOrbit {k} ({A} * (2 * m) + {r}) = {C} * (2 * m) + {b} := by
  have h := Congruence.accOrbit_pow_two_mul_add {k} (2 * m) {r}
  rw [data_{tag}.1, data_{tag}.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_{tag} (m : Nat) :
    acceleratedOrbit {k} ({A} * (2 * m + 1) + {r}) = {C} * (2 * m + 1) + {b} := by
  have h := Congruence.accOrbit_pow_two_mul_add {k} (2 * m + 1) {r}
  rw [data_{tag}.1, data_{tag}.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_{tag} (m : Nat) :
    acceleratedOrbit {k} ({A} * (2 * m) + {r}) < {A} * (2 * m) + {r} ↔ {t} ≤ m := by
  have hc : 3 ^ oddCount {r} {k} < 2 ^ {k} := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_{tag}] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit {k} ({A} * (2 * m) + {r}) < {A} * (2 * m) + {r} ↔ {t} ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_{tag} (m : Nat) :
    acceleratedOrbit {k} ({A} * (2 * m + 1) + {r}) < {A} * (2 * m + 1) + {r} := by
  apply refinement_cleared (k := {k}) (r := {r}) (s := 2) (q := 1)
  · decide
  · rw [cutoff_{tag}]; decide

'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--commit', action='store_true')
    args = parser.parse_args()
    candidates = []
    census = []
    for k in range(2, 13):
        count = exceptions = maximum = 0
        for r in range(1, 2**k):
            a, b = orbit(r, k)
            g = 2**k - 3**a
            if g <= 0:
                continue
            t = 0 if b < r else (b-r)//g + 1
            count += 1
            exceptions += t > 0
            maximum = max(maximum, t)
            candidates.append((k, r, a, b, g, t))
        census.append(dict(depth=k, contracting=count, exceptional=exceptions, max_cutoff=maximum))
    # Include every exceptional class in this census before ordinary classes.
    chosen = sorted(candidates, key=lambda x: (-x[-1], x[0], x[1]))[:900]
    assert len(chosen) == 900 and len({(c[0],c[1]) for c in chosen}) == 900
    assert all(c[-1] in (0, 1) for c in chosen)
    tests = 0
    for k, r, a, b, g, t in chosen:
        for q in (0, 1):
            for m in (0, 1, 2, 17, 1024, 10**12):
                n = 2**k * (2*m+q) + r
                aa, bb = orbit(n, k)
                assert aa == a and bb == 3**a*(2*m+q)+b
                assert (bb < n) == (t <= 2*m+q)
                if q == 0:
                    assert (bb < n) == (t <= m)
                else:
                    assert bb < n
                tests += 1
    BASE.mkdir(parents=True, exist_ok=True)
    run(['lake', 'build', 'Collatz.Research.RefinementAtlas.Core',
         'Collatz.Research.RefinementAtlas.AdaptiveObstruction'])
    files = []
    for i in range(300):
        name = f'Batch{i+1:03}'
        path = BASE / f'{name}.lean'
        source = ('import Collatz.Research.RefinementAtlas.Core\n\n'
                  f'/-! Sharp refined-cylinder certificates, batch {i+1:03}. -/\n'
                  f'namespace Collatz.Research.RefinementAtlas.{name}\n'
                  'open Collatz\nopen Collatz.Research.DescentAtlas\n'
                  'open Collatz.Research.RefinementAtlas\n\n')
        source += ''.join(render_case(*c) for c in chosen[3*i:3*i+3])
        source += f'end Collatz.Research.RefinementAtlas.{name}\n'
        path.write_text(source)
        run(['lake', 'env', 'lean', str(path.relative_to(ROOT))])
        files.append(path)
        if args.commit:
            paths = [str(path.relative_to(ROOT))]
            if i == 0:
                paths += ['scripts/refinement_atlas.py',
                          'Collatz/Research/RefinementAtlas/Core.lean',
                          'Collatz/Research/RefinementAtlas/AdaptiveObstruction.lean']
            if run(['git', 'status', '--porcelain', '--', *paths]):
                run(['git', 'add', '--', *paths])
                run(['git', 'commit', '--only', '-m',
                     f'proof: certify sharp residue refinements {i+1:03}', '--', *paths])
        if (i+1) % 10 == 0:
            print(f'Checked {i+1}/300 batches', flush=True)
    (BASE/'All.lean').write_text('import Collatz.Research.RefinementAtlas.Histogram\n' +
        'import Collatz.Research.RefinementAtlas.AdaptiveObstruction\n' +
        ''.join(f'import Collatz.Research.RefinementAtlas.Batch{i+1:03}\n' for i in range(300)))
    report = dict(cylinders=900, refined_cylinders=1800, batch_theorems=6300,
                  batches=300, lean_lines=sum(len(p.read_text().splitlines()) for p in files),
                  independent_tests=tests, census=census, selected=chosen,
                  method='lake env lean; kernel decide; check before each commit',
                  hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    (BASE/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('cylinders','batch_theorems','lean_lines','independent_tests')}),flush=True)


if __name__ == '__main__':
    main()
