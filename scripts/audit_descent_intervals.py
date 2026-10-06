#!/usr/bin/env python3
"""Build and audit all new public Lean results, with reproducible evidence.

The transitive theorem axiom audit permits only Lean's standard logical axioms.
Two intentionally false certificate mutations must fail normal elaboration.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from descent_intervals import BASELINE, LEAN, REPORT, ROOT, write_or_check

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(sorry|sorryAx|axiom|native_decide|ofReduceBool|skipKernelTC|byAsSorry|addDecl|"
    r"addAndCompile|mkProj|ofReduceNat|evalConst|unsafe|partial|opaque|admit)\b|"
    r"@\[(implemented_by|extern)"
)


def strip_comments(source: str) -> str:
    output, depth, i = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            if not depth or source[i] == '\n':
                output.append(source[i])
            i += 1
    if depth:
        raise RuntimeError("unterminated Lean comment")
    return ''.join(output)


def run_checked(command: list[str], log: str) -> str:
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    (REPORT / log).write_text(output)
    if result.returncode:
        raise RuntimeError(f"command failed: {command}; see {log}")
    return output


def declarations() -> tuple[list[str], list[dict]]:
    names, files = [], []
    for path in sorted(LEAN.glob('*.lean')):
        if path.name == 'Audit.lean':
            continue
        source = path.read_text()
        code = strip_comments(source)
        if FORBIDDEN.search(code):
            raise RuntimeError(f"forbidden proof escape in {path.name}")
        namespaces = re.findall(r'^namespace (\S+)\s*$', code, re.M)
        local = re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)', code, re.M)
        if local and len(namespaces) != 1:
            raise RuntimeError(f"unexpected namespace structure in {path.name}")
        if local:
            names.extend(f'{namespaces[0]}.{name}' for name in local)
        files.append({'path': str(path.relative_to(ROOT)),
                      'sha256': hashlib.sha256(source.encode()).hexdigest(),
                      'lines': len(source.splitlines()),
                      'code_lines': sum(bool(line.strip()) for line in code.splitlines()),
                      'public_theorems': len(local)})
    if len(names) != len(set(names)):
        raise RuntimeError('duplicate declaration in audit')
    return names, files


def audit_axioms(names: list[str]) -> dict:
    audit = LEAN / 'Audit.lean'
    audit.write_text('import Collatz.Research.DescentIntervals.All\n\n' +
                     ''.join(f'#print axioms {name}\n' for name in names))
    output = run_checked(['lake', 'env', 'lean', str(audit)], 'axioms.log')
    no_axioms = set(re.findall(r"'([^']+)' does not depend on any axioms", output))
    dependencies = dict((name, set(re.findall(r'[A-Za-z_][\w.]*', deps)))
                        for name, deps in re.findall(
                            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output))
    observed = no_axioms | set(dependencies)
    if observed != set(names):
        raise RuntimeError(f'axiom output coverage mismatch: missing {set(names)-observed}')
    for name, deps in dependencies.items():
        if deps - ALLOWED:
            raise RuntimeError(f'unapproved dependencies for {name}: {deps-ALLOWED}')
    return {'theorems_checked': len(names), 'without_axioms': len(no_axioms),
            'allowed_logical_axioms': sorted(ALLOWED),
            'observed_axioms': sorted(set().union(*dependencies.values())) if dependencies else []}


def negative_controls() -> list[dict]:
    controls = {
        'zero_exception_removed': 'exactInterval 1 0 = ⟨0, none⟩',
        'late_descent_promoted_to_first': 'exactInterval 5 3 = ⟨0, none⟩',
        'wrong_long_endpoint': 'acceleratedOrbit 59 27 = 24',
    }
    outcomes = []
    for label, claim in controls.items():
        with tempfile.TemporaryDirectory(prefix='collatz-negative-') as directory:
            path = Path(directory) / 'Rejected.lean'
            path.write_text('import Collatz.Research.DescentIntervals.All\n'
                            'open Collatz Collatz.Research.DescentIntervals\n'
                            'set_option maxRecDepth 100000\n'
                            f'example : {claim} := by decide\n')
            result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                    capture_output=True, text=True)
            output = result.stdout + result.stderr
            (REPORT / f'negative-{label}.log').write_text(output.replace(directory, '<temporary-directory>'))
            if (result.returncode == 0 or 'Tactic `decide` proved that the proposition' not in output
                    or '\nis false' not in output):
                raise RuntimeError(f'negative control did not fail as intended: {label}: {output}')
            outcomes.append({'case': label, 'status': 'rejected_false_certificate'})
    return outcomes


def main() -> None:
    manifest = write_or_check(True)
    run_checked(['lake', 'build', 'Collatz.Research.DescentIntervals.All'], 'build.log')
    names, files = declarations()
    axioms = audit_axioms(names)
    controls = negative_controls()
    python_tests = json.loads((REPORT / 'python-tests.json').read_text())
    if python_tests['status'] != 'passed':
        raise RuntimeError('Python checks have not passed')
    report = {'status': 'passed', 'baseline': BASELINE,
              'build_target': 'Collatz.Research.DescentIntervals.All',
              'cylinder_count': manifest['cylinder_count'], 'batch_count': manifest['batch_count'],
              'axiom_audit': axioms, 'negative_controls': controls,
              'lean_lines': sum(f['lines'] for f in files),
              'lean_code_lines_excluding_comments_and_blank': sum(f['code_lines'] for f in files),
              'files': files,
              'limits': ['No proof of Collatz or infinite coverage.',
                         'Historical literature results are context, not new formalizations.',
                         'Generated certificate lines are reported separately from conceptual results.',
                         'This audit builds the new aggregate and its dependencies, not every existing repository target.']}
    (REPORT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'files'}, indent=2))


if __name__ == '__main__':
    main()
