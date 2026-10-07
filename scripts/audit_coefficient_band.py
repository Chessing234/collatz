#!/usr/bin/env python3
"""Kernel build, theorem footprints, seed reproduction, and false-transfer controls."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

NAMES=['CoefficientBand','Band5995']
PREFIX='Collatz.Exploration.'


def main():
    for name in NAMES:
        assert not violations((ROOT/f'Collatz/Exploration/{name}.lean').read_text())
    subprocess.run(['lake','build',PREFIX+'Band5995'],cwd=ROOT,check=True)
    subprocess.run(['python3',str(ROOT/'scripts/test_coefficient_band.py')],cwd=ROOT,check=True)
    count=sum(check_axioms(ROOT/f'Collatz/Exploration/{name}.lean',PREFIX+name) for name in NAMES)
    bad=[
        'example : Collatz.Exploration.CoefficientBand.coefficientCheck 4 1 2 3 1 1 = true := by decide\n',
        'example : Collatz.Exploration.CoefficientBand.coefficientCheck 100 1 1 2 1 1 = true := by decide\n',
        'example : Collatz.Exploration.CoefficientBand.prefixOdds 2 3 = 1 := by decide\n',
        'example : 10*Collatz.orbit 3 3 ≤ 46*3 := by decide\n',
    ]
    rejected=check_false_certificates(PREFIX+'Band5995',bad)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__=='__main__':
    main()
