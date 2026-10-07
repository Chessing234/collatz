#!/usr/bin/env python3
"""Build, independently test, audit axioms, and reject false denominator transfers."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations

MODULE = 'Collatz.Exploration.RationalBandObstruction'
SOURCE = ROOT / 'Collatz/Exploration/RationalBandObstruction.lean'


def main():
    assert not violations(SOURCE.read_text())
    subprocess.run(['lake', 'build', MODULE], cwd=ROOT, check=True)
    subprocess.run(['python3', str(ROOT / 'scripts/test_rational_band_obstruction.py')],
                   cwd=ROOT, check=True)
    count = check_axioms(SOURCE, MODULE)
    prefix = 'Collatz.Exploration.RationalBandObstruction.'
    claims = [
        f'example : {prefix}denominatorOrbit 5 8 23 = 24 := by decide\n',
        f'example : {prefix}denominatorStep 1 23 = 74 := by decide\n',
        f'example : {prefix}denominatorOrbit 10 8 46 = 46 := by decide\n',
        'example : Collatz.orbit 8 11 = 11 := by decide\n',
    ]
    rejected = check_false_certificates(MODULE, claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false transfers rejected')


if __name__ == '__main__':
    main()
