#!/usr/bin/env python3
"""Generate 1,000 disjoint, kernel-checked depth-15 certificate units.

The large output is proof-carrying data, not independent discoveries. Every
commit contains new infinite-class statements and follows a successful build.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time
from descent_intervals import exact_interval, trace, row_source
from stopping_atlas import git_write

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / 'Collatz/Research/PassageAtlas'
REPORT = ROOT / 'Research/PassageAtlas'
BASELINE = 'c96b95946b896306b1252b553781ef270bb3f32d'
DEPTH = 15
BATCH_COUNT = 1000
HORIZON = 2592
THRESHOLD = 330588
SMALL_HORIZON = 164


def small_files():
    """Extend the inherited certificate instead of recomputing its old range."""
    files = {}
    files[LEAN / 'SmallBase.lean'] = '''import Collatz.Strategy.FirstLight1024

namespace Collatz.Research.PassageAtlas
open FirstLightScan

/-- Reuse the inherited checked range at the enlarged scan horizon. -/
theorem prefix_99730 : checkInterval 164 0 99730 = true :=
  checkInterval_mono_horizon 135 164 0 99730 (by decide)
    FirstLight1024Chunks.prefix_99730

end Collatz.Research.PassageAtlas
'''
    starts = list(range(99730, THRESHOLD, 2048))
    for i, start in enumerate(starts):
        length = min(2048, THRESHOLD - start)
        end = start + length
        prev = 'SmallBase' if i == 0 else f'Small{i-1:03}'
        files[LEAN / f'Small{i:03}.lean'] = f'''import Collatz.Research.PassageAtlas.{prev}

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_{i:03} : checkInterval {SMALL_HORIZON} {start} {length} = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_{end} : checkInterval {SMALL_HORIZON} 0 {end} = true :=
  checkInterval_append {SMALL_HORIZON} 0 {start} {length}
    prefix_{start} small_block_{i:03}

end Collatz.Research.PassageAtlas
'''
    files[LEAN / 'SmallInputs.lean'] = f'''import Collatz.Research.PassageAtlas.Small{len(starts)-1:03}

namespace Collatz.Research.PassageAtlas
open FirstLightDescent FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Every exceptional input above one has a first-crossing descent by 164. -/
theorem small_starts_330588 : ∀ n : Fin 330588, 1 < n.val →
    ∃ k : Fin 165, FirstLight n.val k.val ∧ acceleratedOrbit k.val n.val < n.val := by
  intro n hn
  exact checkInterval_sound 164 0 330588 prefix_330588 n.val (by omega) n.isLt hn

/-- A witness attaining the small-input crossing horizon; it is not a counterexample. -/
theorem small_horizon_attained : FirstLight 270271 164 ∧ acceleratedOrbit 164 270271 < 270271 := by decide

end Collatz.Research.PassageAtlas
'''
    return files


def census_source(rows):
    chunks = 128
    s = '''import Collatz.Research.StoppingAtlas.Census

namespace Collatz.Research.PassageAtlas
open PeriodicCounting Collatz.Research.StoppingAtlas
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem census_prefix_0 : countBelow (firstEventB 15) 0 = 0 := rfl

'''
    total = 0
    for j, base in enumerate(range(0, 1 << DEPTH, chunks)):
        # firstEventB shifts by two; reducing modulo the period is legitimate.
        count = sum(rows[(n + 2) % (1 << DEPTH)]['kind'] == 'tail'
                    for n in range(base, base + chunks))
        s += f'''/-- Ordinary kernel reduction on a translated 128-input block. -/
theorem census_chunk_{j} : countBelow (fun n => firstEventB 15 ({base} + n)) 128 = {count} := by decide

theorem census_prefix_{j+1} : countBelow (firstEventB 15) {base+chunks} = {total+count} := by
  have h := count_shift_add (firstEventB 15) {base} 128
  rw [census_prefix_{j}, census_chunk_{j}] at h
  exact h

'''
        total += count
    s += f'''/-- Complete period numerator, checked independently of the cylinder classifier. -/
theorem period_count_fifteen : countBelow (firstEventB 15) (2 ^ 15) = {total} := census_prefix_256

/-- Composition-sensitive count bound at every finite cutoff. -/
theorem depth_fifteen_error (N : Nat) :
    32768 * countBelow (firstEventB 15) N ≤ N * {total} + {total*((1<<DEPTH)-total)} ∧
    N * {total} ≤ 32768 * countBelow (firstEventB 15) N + {total*((1<<DEPTH)-total)} := by
  have h := firstEvent_composition_error 15 N
  dsimp only at h
  rw [period_count_fifteen] at h
  simpa only [show (2 : Nat) ^ 15 = 32768 by decide,
    show (32768 - {total} : Nat) = {(1<<DEPTH)-total} by decide,
    show ({total} * {(1<<DEPTH)-total} : Nat) = {total*((1<<DEPTH)-total)} by decide] using h

end Collatz.Research.PassageAtlas
'''
    return s


def generated():
    rows = []
    for r in range(1 << DEPTH):
        states, counts = trace(r, DEPTH)
        interval = exact_interval(DEPTH, r)
        rows.append({'depth': DEPTH, 'residue': r, 'odd_count': counts[-1],
                     'endpoint': states[-1], 'lower': interval.lower,
                     'upper': interval.upper, 'kind': interval.kind})
    files, batches = small_files(), []
    for i in range(BATCH_COUNT):
        start = len(rows) * i // BATCH_COUNT
        stop = len(rows) * (i + 1) // BATCH_COUNT
        name = f'Batch{i+1:04}'
        source = ('import Collatz.Research.DescentIntervals.Classifier\n\n'
                  f'namespace Collatz.Research.PassageAtlas.{name}\n\n'
                  'open Collatz.Research.DescentIntervals\n\n'
                  'set_option maxRecDepth 20000\nset_option maxHeartbeats 0\n\n')
        source += ''.join(row_source(row) for row in rows[start:stop])
        source += f'end Collatz.Research.PassageAtlas.{name}\n'
        files[LEAN / f'{name}.lean'] = source
        batches.append({'module': name, 'start': start, 'stop': stop,
                        'sha256': hashlib.sha256(source.encode()).hexdigest()})
    files[LEAN / 'Certificates.lean'] = ''.join(
        f'import Collatz.Research.PassageAtlas.{b["module"]}\n' for b in batches)
    files[LEAN / 'Census.lean'] = census_source(rows)
    return files, {'baseline': BASELINE, 'depth': DEPTH, 'batch_count': BATCH_COUNT,
                   'horizon': HORIZON, 'threshold': THRESHOLD,
                   'small_horizon': SMALL_HORIZON, 'cylinder_count': len(rows),
                   'certificate_theorems': 4 * len(rows), 'batches': batches, 'rows': rows}


def write_or_check(check=False):
    files, manifest = generated()
    files[REPORT / 'manifest.json'] = json.dumps(manifest, indent=2) + '\n'
    for path, source in files.items():
        if check:
            if not path.is_file() or path.read_text() != source:
                raise RuntimeError(f'generated output differs: {path.relative_to(ROOT)}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
    print(f'{"Checked" if check else "Generated"} {len(manifest["rows"])} new cylinders in {BATCH_COUNT} batches', flush=True)
    return manifest


def checked_build(batch):
    begin = time.monotonic()
    p = subprocess.run(['lake', 'build', f'Collatz.Research.PassageAtlas.{batch["module"]}'],
                       cwd=ROOT, capture_output=True, text=True)
    output = p.stdout + p.stderr
    if p.returncode:
        (REPORT / f'{batch["module"]}.failure.log').write_text(output)
        raise RuntimeError(f'kernel rejected {batch["module"]}')
    return {'module': batch['module'], 'source_sha256': batch['sha256'],
            'build_exit_code': 0, 'seconds': round(time.monotonic() - begin, 3),
            'build_output_sha256': hashlib.sha256(output.encode()).hexdigest()}


def commit_batches(manifest, jobs):
    subprocess.run(['lake', 'build', 'Collatz.Research.DescentIntervals.Classifier'], cwd=ROOT, check=True)
    receipt_path = REPORT / 'batch-receipts.json'
    previous = {r['module']: r for r in json.loads(receipt_path.read_text())} if receipt_path.exists() else {}
    receipts = []

    def check_or_reuse(batch):
        prior = previous.get(batch['module'])
        relative = f"Collatz/Research/PassageAtlas/{batch['module']}.lean"
        if prior and prior.get('build_exit_code') == 0 and prior.get('source_sha256') == batch['sha256']:
            last = subprocess.check_output(['git', 'log', '-1', '--format=%H', '--', relative],
                                           cwd=ROOT, text=True).strip()
            current_hash = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
            clean = subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', relative], cwd=ROOT).returncode == 0
            if last == prior.get('commit') and clean and current_hash == batch['sha256']:
                # Reuse only an already committed, byte-identical certificate.
                # The final build and history audit independently recheck it.
                return dict(prior)
        return checked_build(batch)

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        results = pool.map(check_or_reuse, manifest['batches'])
        for batch, receipt in zip(manifest['batches'], results):
            relative = f'Collatz/Research/PassageAtlas/{batch["module"]}.lean'
            tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', relative], cwd=ROOT,
                                     capture_output=True).returncode == 0
            clean = tracked and subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', relative], cwd=ROOT).returncode == 0
            if not clean:
                git_write(['add', '--', relative])
                first, last = manifest['rows'][batch['start']], manifest['rows'][batch['stop']-1]
                message = f'proof: certify passage {batch["module"]} (15:{first["residue"]} to 15:{last["residue"]})'
                git_write(['commit', '--only', '-m', message, '--', relative])
            receipt['commit'] = subprocess.check_output(['git', 'log', '-1', '--format=%H', '--', relative],
                                                       cwd=ROOT, text=True).strip()
            receipts.append(receipt)
            (REPORT / 'batch-receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
            if len(receipts) % 25 == 0 or len(receipts) == 1:
                print(f'{len(receipts)}/1000 certified commits; {batch["stop"]} distinct classes', flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    p.add_argument('--commit', action='store_true')
    p.add_argument('--jobs', type=int, default=1)
    args = p.parse_args()
    if not 1 <= args.jobs <= 8:
        p.error('jobs must be between 1 and 8')
    if args.check and args.commit:
        p.error('--check is read-only; use --commit without --check')
    manifest = write_or_check(args.check)
    if args.commit:
        commit_batches(manifest, args.jobs)

if __name__ == '__main__':
    main()
