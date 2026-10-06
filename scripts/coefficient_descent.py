#!/usr/bin/env python3
"""Reproducible finite witnesses for a conditional 256-step crossing theorem.

The output supplies distinct finite inputs and infinite dyadic rays. Certificate
batches are checked before commits; they are not separate mathematical discoveries.
Only standard-library exact integers are used. No conjecture is assumed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'Collatz/Research/CoefficientDescent'
REPORT = ROOT / 'Research/CoefficientDescent'
BASELINE = '0b0fa49f1dab57e4bc8790b0c09121b7162ce28c'
HORIZON = 256
BOUND = 6701
BATCH_COUNT = 100


def crossing(n: int, limit: int = 10000) -> dict:
    """Find the first coefficient crossing, independently of the interval solver."""
    if type(n) is not int or n < 2:
        raise ValueError('crossing witnesses require integer n >= 2')
    state, power, denominator, odds = n, 1, 1, 0
    for k in range(1, limit + 1):
        if state & 1:
            state = (3 * state + 1) // 2
            power *= 3
            odds += 1
        else:
            state //= 2
        denominator *= 2
        if power < denominator:
            if state >= n:
                raise RuntimeError(f'coefficient crossing without descent: n={n}, k={k}')
            return {'n': n, 'k': k, 'odd_count': odds, 'endpoint': state}
    raise RuntimeError(f'no crossing within {limit} steps for {n}')


def gap_bound(horizon: int) -> tuple[int, dict]:
    """Least uniform integer bound for the published accumulator inequality."""
    best, critical = 0, {}
    for k in range(1, horizon + 1):
        a, p = 0, 1
        while 3 * p < 2 ** k:
            a, p = a + 1, p * 3
        required = a * p // (3 * (2 ** k - p)) + 1
        if required > best:
            best = required
            critical = {'k': k, 'a': a, 'numerator': a * p,
                        'denominator': 3 * (2 ** k - p)}
    return best, critical


def batch_source(name: str, rows: list[dict]) -> str:
    lo, hi = rows[0]['n'], rows[-1]['n'] + 2
    pieces = ['import Collatz.Research.CoefficientDescent.Basic\n\n',
              f'namespace Collatz.Research.CoefficientDescent.{name}\n\n',
              'open FirstDescentClass\n\nset_option maxRecDepth 20000\n',
              'set_option maxHeartbeats 0\n\n']
    for row in rows:
        n, k = row['n'], row['k']
        pieces.append(f'''/-- Checked base and every prefix for input {n}. -/
theorem certificate_{n} : classCertificateB {k} {n} = true := by
  decide

/-- The same exact first-descent time holds on an infinite dyadic ray. -/
theorem ray_{n} (m : Nat) : stoppingTime (2 ^ {k} * m + {n}) {k} :=
  stoppingTime_of_classCertificate certificate_{n} m

''')
    alternatives = ' ∨ '.join(f'n = {row["n"]}' for row in rows)
    pieces.append(f'''/-- Exhaustive coverage of the odd inputs in this batch, with no gaps. -/
theorem coverage : CertifiedRange {lo} {hi} := by
  intro n hlo hhi hodd
  have hn : {alternatives} := by omega
  rcases hn with {" | ".join("h" for _ in rows)}
''')
    for row in rows:
        pieces.append(f'  · subst n\n    exact ⟨{row["k"]}, witness_of_certificate certificate_{row["n"]}⟩\n')
    pieces.append(f'\nend Collatz.Research.CoefficientDescent.{name}\n')
    return ''.join(pieces)


def generated() -> tuple[dict[Path, str], dict]:
    required, critical = gap_bound(HORIZON)
    if required != BOUND:
        raise RuntimeError('incorrect uniform failure bound')
    rows = [crossing(n) for n in range(3, BOUND, 2)]
    files, batches = {}, []
    for i in range(BATCH_COUNT):
        start, stop = len(rows) * i // BATCH_COUNT, len(rows) * (i + 1) // BATCH_COUNT
        selected = rows[start:stop]
        name = f'Batch{i + 1:03}'
        source = batch_source(name, selected)
        files[LEAN / f'{name}.lean'] = source
        batches.append({'module': name, 'lo': selected[0]['n'], 'hi': selected[-1]['n'] + 2,
                        'rows': len(selected), 'sha256': hashlib.sha256(source.encode()).hexdigest()})
    imports = ''.join(f'import Collatz.Research.CoefficientDescent.{b["module"]}\n' for b in batches)
    chain = 'Batch100.coverage'
    for b in reversed(batches[:-1]):
        chain = f'{b["module"]}.coverage.append (\n    {chain})'
    files[LEAN / 'SmallInputs.lean'] = imports + f'''
namespace Collatz.Research.CoefficientDescent

open FirstLightDescent

/-- All odd starts that can evade the uniform large-input inequality. -/
theorem small_odd : CertifiedRange 3 {BOUND} :=
  {chain}

/-- Even inputs are discharged symbolically; every remaining small input has a witness. -/
theorem small_inputs (n : Nat) (hn : 1 < n) (hb : n < {BOUND}) :
    ∃ k, FirstLight n k ∧ acceleratedOrbit k n < n := by
  rcases Arith.mod_two_eq_zero_or_one n with he | ho
  · exact ⟨1, even_witness (by omega) he⟩
  · exact small_odd n (by omega) hb ho

end Collatz.Research.CoefficientDescent
'''
    manifest = {'baseline': BASELINE, 'horizon': HORIZON, 'failure_bound': BOUND,
                'critical_gap': critical, 'batch_count': BATCH_COUNT,
                'odd_witness_count': len(rows), 'max_witness_time': max(row['k'] for row in rows),
                'batches': batches, 'rows': rows}
    return files, manifest


def write_or_check(check: bool = False) -> dict:
    files, manifest = generated()
    files[REPORT / 'manifest.json'] = json.dumps(manifest, indent=2) + '\n'
    for path, source in files.items():
        if check:
            if not path.is_file() or path.read_text() != source:
                raise RuntimeError(f'generated source mismatch: {path.relative_to(ROOT)}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
    print(f'{"Checked" if check else "Generated"} {len(manifest["rows"])} witnesses in {BATCH_COUNT} batches', flush=True)
    return manifest


def commit_batches(manifest: dict) -> None:
    for batch in manifest['batches']:
        name = batch['module']
        relative = f'Collatz/Research/CoefficientDescent/{name}.lean'
        result = subprocess.run(['lake', 'build', f'Collatz.Research.CoefficientDescent.{name}'],
                                cwd=ROOT, capture_output=True, text=True)
        (REPORT / f'{name}.build.log').write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(f'Lean rejected {name}; see {name}.build.log')
        tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', relative],
                                 cwd=ROOT, capture_output=True).returncode == 0
        if tracked and subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', relative], cwd=ROOT).returncode == 0:
            print(f'{name}: already committed, rechecked', flush=True)
            continue
        subprocess.run(['git', 'add', '--', relative], cwd=ROOT, check=True)
        message = f'proof: certify coefficient descent on odd inputs [{batch["lo"]}, {batch["hi"]})'
        subprocess.run(['git', 'commit', '--only', '-m', message, '--', relative],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
        print(f'{name}: checked and committed {batch["rows"]} witnesses', flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--commit', action='store_true')
    args = parser.parse_args()
    manifest = write_or_check(args.check)
    if args.commit:
        commit_batches(manifest)


if __name__ == '__main__':
    main()
