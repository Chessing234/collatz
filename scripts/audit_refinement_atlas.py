#!/usr/bin/env python3
"""Build the full atlas and check every exported theorem's axiom dependencies."""
import hashlib
import json
import re
from pathlib import Path
from refinement_atlas import ROOT, BASE, run


def main():
    report = json.loads((BASE/'verification.json').read_text())
    source_files = sorted(BASE.glob('*.lean'))
    audited = []
    for path in source_files:
        source = path.read_text()
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', source):
            raise RuntimeError(f'Untrusted source declaration in {path}')
        if path.name in report['hashes']:
            assert hashlib.sha256(path.read_bytes()).hexdigest() == report['hashes'][path.name]
        namespace = re.search(r'^namespace (\S+)', source, re.M)
        if not namespace:
            continue
        for name in re.findall(r'^theorem (\w+)', source, re.M):
            audited.append(namespace.group(1)+'.'+name)
    audit = BASE/'Audit.lean'
    audit.write_text('import Collatz.Research.RefinementAtlas.All\n' +
                     ''.join(f'#print axioms {name}\n' for name in audited))
    build_parts = []
    batches = sorted(BASE.glob('Batch*.lean'))
    # Bound the number of simultaneous compiler processes on a shared desktop.
    for i in range(0, len(batches), 6):
        modules = ['Collatz.Research.RefinementAtlas.'+p.stem for p in batches[i:i+6]]
        build_parts.append(run(['lake', 'build', *modules]))
        if (i+6) % 30 == 0:
            print(f'Built {min(i+6,len(batches))}/300 modules for axiom audit', flush=True)
    build_parts.append(run(['lake', 'build', 'Collatz.Research.RefinementAtlas.All']))
    build = ''.join(build_parts)
    (BASE/'build.log').write_text(build)
    output = run(['lake', 'env', 'lean', str(audit.relative_to(ROOT))])
    (BASE/'axioms.log').write_text(output)
    statements = output.count('depends on axioms') + output.count('does not depend on any axioms')
    assert statements == len(audited), (statements, len(audited))
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    dependencies = set()
    for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output):
        dependencies.update(x.strip() for x in group.split(',') if x.strip())
    assert dependencies <= allowed, dependencies
    messages = run(['git', 'log', '--format=%s']).splitlines()
    expected = {f'proof: certify sharp residue refinements {i:03}' for i in range(1,301)}
    actual = [x for x in messages if x in expected]
    assert len(actual) == 300 and set(actual) == expected
    assert report['lean_lines'] >= 20000
    result = dict(theorems_audited=len(audited), axioms=sorted(dependencies),
                  batch_lines=report['lean_lines'], batch_commits=len(actual),
                  hashes_checked=len(report['hashes']), full_build='passed',
                  source_integrity='passed', axiom_audit='passed')
    (BASE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
