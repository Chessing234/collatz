#!/usr/bin/env python3
"""Audit the universal near-six bounds and necessary clock-width inequality."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

MODULE='Collatz.Exploration.BalancedNearSix'


def main():
    source=ROOT/'Collatz/Exploration/BalancedNearSix.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',MODULE],cwd=ROOT,check=True)
    subprocess.run(['python3',str(ROOT/'scripts/test_balanced_near_six.py')],cwd=ROOT,check=True)
    count=check_axioms(source,MODULE)
    bad=[
        'example : 2*Collatz.orbit 3 19 ≤ (6*2-3)*19 := by decide\n',
        'example : 1*5+2*1 ≤ 6*1*1 := by decide\n',
        'example : 1*1+2*0 ≤ 6*1*0 := by decide\n',
        'example : 2*16 < 1*2^5 := by decide\n',
    ]
    rejected=check_false_certificates(MODULE,bad)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__=='__main__':
    main()
