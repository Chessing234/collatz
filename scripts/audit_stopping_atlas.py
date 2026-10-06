#!/usr/bin/env python3
"""Build the full addition, audit every theorem, and reject false controls."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from stopping_atlas import BASELINE, LEAN, REPORT, ROOT, write_or_check
from audit_descent_intervals import ALLOWED, FORBIDDEN, strip_comments


def run(command: list[str], log: str) -> str:
    with (REPORT / log).open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, text=True)
    output = (REPORT / log).read_text()
    if result.returncode:
        raise RuntimeError(f'command failed: {command}; see {log}')
    return output


def sources() -> tuple[list[str], list[dict]]:
    names, records = [], []
    for path in sorted(LEAN.glob('*.lean')):
        if path.name == 'Audit.lean':
            continue
        source = path.read_text()
        code = strip_comments(source)
        if FORBIDDEN.search(code):
            raise RuntimeError(f'forbidden proof escape in {path.name}')
        namespaces = re.findall(r'^namespace (\S+)\s*$', code, re.M)
        local = re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+([\w.]+)', code, re.M)
        if local and len(namespaces) != 1:
            raise RuntimeError(f'unexpected namespace shape in {path.name}')
        if local:
            names.extend(f'{namespaces[0]}.{name}' for name in local)
        records.append({'path': str(path.relative_to(ROOT)),
                        'sha256': hashlib.sha256(source.encode()).hexdigest(),
                        'lines': len(source.splitlines()),
                        'code_lines': sum(bool(line.strip()) for line in code.splitlines()),
                        'theorems': len(local)})
    if len(names) != len(set(names)):
        raise RuntimeError('duplicate declaration name')
    return names, records


def axioms(names: list[str]) -> dict:
    path = LEAN / 'Audit.lean'
    path.write_text('import Collatz.Research.StoppingAtlas.All\n\n' +
                    ''.join(f'#print axioms {name}\n' for name in names))
    output = run(['lake', 'env', 'lean', str(path)], 'axioms.log')
    none = set(re.findall(r"'([^']+)' does not depend on any axioms", output))
    deps = {name: set(re.findall(r'[A-Za-z_][\w.]*', values)) for name, values in
            re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)}
    if none | set(deps) != set(names):
        raise RuntimeError('axiom audit did not cover precisely every theorem')
    for name, values in deps.items():
        if values - ALLOWED:
            raise RuntimeError(f'unexpected axioms for {name}: {values}')
    return {'theorems_checked': len(names), 'without_axioms': len(none),
            'allowed': sorted(ALLOWED), 'observed': sorted(set().union(*deps.values()))}


def negative_controls() -> list[dict]:
    claims = {
        'missing_small_input_exception': 'acceleratedOrbit 2 1 < 1',
        'wrong_cylinder': '(Research.DescentIntervals.exactInterval 11 27).upper = none',
        'insufficient_gap_bound': '(971 : Nat) * 3 ^ 971 < 3 * (2 ^ 1539 - 3 ^ 971) * 99730',
        'late_descent_is_not_first': 'FirstLightDescent.FirstLight 3 5',
    }
    outcomes = []
    for label, claim in claims.items():
        with tempfile.TemporaryDirectory(prefix='collatz-atlas-negative-') as directory:
            path = Path(directory) / 'Rejected.lean'
            path.write_text('import Collatz.Research.StoppingAtlas.All\n'
                            'open Collatz\nset_option maxRecDepth 100000\nset_option exponentiation.threshold 2048\n'
                            f'example : {claim} := by decide\n')
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                    capture_output=True, text=True)
            output = result.stdout + result.stderr
            (REPORT / f'negative-{label}.log').write_text(output.replace(directory, '<temporary-directory>'))
            if result.returncode == 0 or 'Tactic `decide` proved that the proposition' not in output or '\nis false' not in output:
                raise RuntimeError(f'negative control failed for the wrong reason: {label}: {output}')
            outcomes.append({'case': label, 'status': 'rejected_false_certificate'})
    return outcomes


def main() -> None:
    manifest = write_or_check(True)
    run(['lake', 'build', 'Collatz.Research.StoppingAtlas.All'], 'build.log')
    names, records = sources()
    negative = negative_controls()
    footprints = axioms(names)
    run(['python3', 'scripts/test_stopping_atlas.py'], 'python-tests.log')
    tests = json.loads((REPORT / 'python-tests.json').read_text())
    if tests['status'] != 'passed':
        raise RuntimeError('independent Python tests did not pass')
    generated_records = [r for r in records if (Path(r['path']).name.startswith('Batch') or Path(r['path']).name in {'Census.lean', 'Certificates.lean'})]
    report = {'status': 'passed', 'baseline': BASELINE,
              'target': 'Collatz.Research.StoppingAtlas.All',
              'horizon': 1538, 'failure_bound': 99730,
              'cylinder_count': manifest['cylinder_count'], 'batch_count': manifest['batch_count'],
              'lean_lines': sum(r['lines'] for r in records),
              'lean_code_lines': sum(r['code_lines'] for r in records),
              'generated_lean_code_lines': sum(r['code_lines'] for r in generated_records),
              'handwritten_lean_code_lines': sum(r['code_lines'] for r in records if r not in generated_records
                                                and not r['path'].endswith('SmallInputs.lean')),
              'axiom_audit': footprints, 'negative_controls': negative,
              'python_tests': tests, 'files': records,
              'scope': ['Build covers the addition and all its dependencies.',
                        'Does not rebuild every historical repository target or the separate Mathlib extension.',
                        'Standard kernel checking: no added axioms, sorry, or native_decide.',
                        'Finite certificate count is not a count of independent mathematical discoveries.',
                        'No universal existence of coefficient crossings or proof of Collatz.']}
    if report['lean_code_lines'] < 100000:
        raise RuntimeError('requested new code-line minimum not met')
    (REPORT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'files'}, indent=2))


if __name__ == '__main__':
    main()
