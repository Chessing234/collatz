#!/usr/bin/env python3
"""Build the new module, inspect every theorem's axioms, reject false certificates."""
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'Collatz/Exploration/BarrierKernel.lean'


def lean_check(text):
    with tempfile.TemporaryDirectory(prefix='collatz-barrier-') as directory:
        path = Path(directory) / 'Audit.lean'
        path.write_text('import Collatz.Exploration.BarrierKernel\n' + text)
        return subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                              capture_output=True, text=True)


def main():
    subprocess.run(['lake', 'build', 'Collatz.Exploration.BarrierKernel'],
                   cwd=ROOT, check=True)
    subprocess.run(['python3', str(ROOT / 'scripts/test_barrier_kernel.py')],
                   cwd=ROOT, check=True)
    names = re.findall(r'^theorem (\w+)', SOURCE.read_text(), re.MULTILINE)
    assert names
    audit = lean_check(''.join(f'#print axioms Collatz.Exploration.BarrierKernel.{name}\n'
                               for name in names))
    assert audit.returncode == 0, audit.stdout + audit.stderr
    footprints = re.findall(
        r"'Collatz\.Exploration\.BarrierKernel\.(\w+)' "
        r'(?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])',
        audit.stdout)
    assert [name for name, _ in footprints] == names, audit.stdout
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in footprints:
        found = {axiom.strip() for axiom in axioms.split(',') if axiom.strip()}
        assert found <= allowed, (name, found)
    # Intentionally false finite claims must fail kernel checking.
    bad = [
        'example : Collatz.Exploration.BarrierKernel.intervalCheck 3 10 8 3 = true := by decide\n',
        'example : Collatz.Exploration.BarrierKernel.intervalCheck 2 4 3 4 = true := by decide\n',
    ]
    for claim in bad:
        result = lean_check(claim)
        assert result.returncode != 0, claim
        assert 'Tactic `decide` proved that the proposition' in result.stdout, result.stdout + result.stderr
        assert 'is false' in result.stdout, result.stdout + result.stderr
    print(f'{len(names)} theorem axiom footprints checked; {len(bad)} false certificates rejected')


if __name__ == '__main__':
    main()
