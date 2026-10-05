#!/usr/bin/env python3
"""Build and audit the self-contained finite shadow-diversity development.

Historical boundary/summability modules are deliberately outside this audit.
Four attributed grid lemmas are reused; the other endpoints extend them.
"""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification'
MODULES = ['ShadowGridCore', 'ShadowReturnArithmetic',
           'ShadowWindowDiversity', 'ShadowQuantization']
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}


def stamp():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def code_only(source):
    # Lean block comments nest. Strings are retained; these proof files use
    # no metaprogramming or string-based elaboration.
    output, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n':
                output.append('\n')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            output.append(source[i])
            i += 1
    assert depth == 0, 'Unclosed comment'
    return ''.join(output)


def run(args, logfile):
    env = dict(os.environ)
    env.setdefault('LEAN_NUM_THREADS', '2')
    with (OUT / logfile).open('w') as stream:
        result = subprocess.run(args, cwd=ROOT, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    assert result.returncode == 0, f'Command failed: {args}; see {logfile}'
    return (OUT / logfile).read_text()


def main():
    OUT.mkdir(exist_ok=True)
    destination = OUT / 'shadow-window-report.json'
    report = {'status': 'in_progress', 'started_utc': stamp(),
              'scope': 'Four standalone Mathlib modules and all their theorem endpoints; historical Collatz boundary development not rebuilt.'}
    destination.write_text(json.dumps(report, indent=2)+'\n')
    try:
        sources = [ROOT / 'CollatzTargetDensity' / (m+'.lean') for m in MODULES]
        endpoints = []
        for module, path in zip(MODULES, sources):
            code = code_only(path.read_text())
            assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|run_tac|elab|macro)\b|\[extern|implemented_by', code), path
            endpoints += ['CollatzTargetDensity.'+module+'.'+name for name in
                          re.findall(r'^theorem\s+(\w+)', code, re.M)]
        audit = ROOT / 'Verification' / 'ShadowWindowDiversity.lean'
        listed = re.findall(r'^#print axioms (\S+)', audit.read_text(), re.M)
        assert len(listed) == len(set(listed))
        assert set(listed) == set(endpoints), 'Audit coverage mismatch'
        fingerprinted = sources + [audit, Path(__file__).resolve(),
                                    ROOT.parent / 'scripts' / 'shadow_window_probe.py']
        report['source_sha256'] = {str(p.relative_to(ROOT.parent)): digest(p) for p in fingerprinted}
        vendor = ROOT / 'vendor' / 'positive-density-log-time-collatz'
        packages = json.loads((vendor/'lake-manifest.json').read_text())['packages']
        revisions = {}
        for package in packages:
            checkout = vendor / '.lake' / 'packages' / package['name']
            revision = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip()
            assert revision == package['rev'], f'Wrong dependency: {package["name"]}'
            subprocess.run(['git', '-C', str(checkout), 'diff', '--exit-code', '--quiet', '--', '*.lean'], check=True)
            revisions[package['name']] = revision
        report['dependency_revisions'] = revisions
        report['lean_toolchain'] = (ROOT/'lean-toolchain').read_text().strip()
        print('Sources and pinned dependencies checked; building the four-module target.', flush=True)
        run(['lake', 'build', '+CollatzTargetDensity.ShadowQuantization:olean'],
            'shadow-window-build.log')
        print('Target build passed; checking every transitive axiom footprint.', flush=True)
        evidence = run(['lake', 'env', 'lean', 'Verification/ShadowWindowDiversity.lean'],
                       'shadow-window-axioms.log')
        footprints = {}
        for name in endpoints:
            match = re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]", evidence, re.S)
            if match:
                axioms = {a.strip() for a in match.group(1).split(',') if a.strip()}
            else:
                assert f"'{name}' does not depend on any axioms" in evidence, name
                axioms = set()
            assert axioms <= ALLOWED, (name, axioms - ALLOWED)
            footprints[name] = sorted(axioms)
        for path in fingerprinted:
            assert digest(path) == report['source_sha256'][str(path.relative_to(ROOT.parent))], 'Source changed during verification'
        report.update(status='verified', theorem_count=len(endpoints),
                      reused_grid_theorems=4, new_development_endpoints=len(endpoints)-4,
                      axioms=footprints, finished_utc=stamp())
    except Exception as error:
        report.update(status='failed', error=str(error), finished_utc=stamp())
        destination.write_text(json.dumps(report, indent=2)+'\n')
        raise
    destination.write_text(json.dumps(report, indent=2)+'\n')
    print(f'Verified {len(endpoints)} theorem endpoints. Report: {destination}', flush=True)


if __name__ == '__main__':
    main()
