"""Targeted source, dependency, build, and transitive axiom audit."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'vendor/positive-density-log-time-collatz'
OUT = ROOT / 'Verification'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    report = {'status': 'in_progress', 'started': datetime.now(timezone.utc).isoformat(),
              'scope': 'HeavySuffix and its imported proof dependencies; not all historical endpoints'}
    destination = OUT / 'heavy-suffix-report.json'
    destination.write_text(json.dumps(report, indent=2) + '\n')
    try:
        manifest = json.loads((VENDOR / 'source-manifest.json').read_text())
        for entry in manifest['source_files']:
            p = (VENDOR / entry['path']).resolve()
            assert p.is_relative_to(VENDOR.resolve())
            assert digest(p) == entry['sha256'], f'Changed upstream source: {p}'
        report['upstream_sources_checked'] = len(manifest['source_files'])
        revisions = {}
        for pkg in json.loads((VENDOR / 'lake-manifest.json').read_text())['packages']:
            got = subprocess.check_output(['git', '-C', str(VENDOR / '.lake/packages' / pkg['name']),
                                           'rev-parse', 'HEAD'], text=True).strip()
            assert got == pkg['rev'], f'Changed dependency: {pkg["name"]}'
            revisions[pkg['name']] = got
        report['dependency_revisions'] = revisions
        sources = list((ROOT / 'CollatzTargetDensity').glob('*.lean'))
        sources += [ROOT / 'Verification/HeavySuffix.lean', Path(__file__).resolve()]
        hashes = {str(p.relative_to(ROOT)): digest(p) for p in sources}
        report['source_sha256'] = hashes
        source = (ROOT / 'CollatzTargetDensity/HeavySuffix.lean').read_text()
        assert not re.search(r'\b(sorry|axiom|unsafe|native_decide)\b', source)
        names = ['CollatzTargetDensity.HeavySuffix.' + x for x in
                 re.findall(r'^theorem\s+(\w+)', source, re.M)]
        audit = (ROOT / 'Verification/HeavySuffix.lean').read_text()
        assert re.findall(r'^#print axioms (\S+)', audit, re.M) == names
        for args, log in [(['lake', 'build', '+CollatzTargetDensity.HeavySuffix:olean'], 'heavy-suffix-build.log'),
                          (['lake', 'env', 'lean', 'Verification/HeavySuffix.lean'], 'heavy-suffix-axioms.log')]:
            with (OUT / log).open('w') as f:
                subprocess.run(args, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT, check=True)
        evidence = (OUT / 'heavy-suffix-axioms.log').read_text()
        footprints = {}
        for name in names:
            match = re.search("'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", evidence)
            assert match, f'Missing axiom footprint: {name}'
            axioms = {x.strip() for x in match[1].split(',') if x.strip()}
            assert axioms <= ALLOWED, f'Unexpected axioms: {name}'
            footprints[name] = sorted(axioms)
        for p in sources:
            assert digest(p) == hashes[str(p.relative_to(ROOT))], f'Source changed during audit: {p}'
        report.update(status='verified', theorem_count=len(names), axioms=footprints,
                      lean_toolchain=(ROOT / 'lean-toolchain').read_text().strip())
    except Exception as e:
        report.update(status='failed', error=str(e))
        raise
    finally:
        report['finished'] = datetime.now(timezone.utc).isoformat()
        destination.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Verified {len(names)} HeavySuffix endpoints.')

if __name__ == '__main__':
    main()
