#!/usr/bin/env python3
"""Build, audit every new theorem, and reject false offset/quantifier transfers."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations

MODULE = 'Collatz.Exploration.BalancedOffset'


def main():
    source=ROOT/'Collatz/Exploration/BalancedOffset.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',MODULE],cwd=ROOT,check=True)
    subprocess.run(['python3',str(ROOT/'scripts/test_balanced_offset.py')],cwd=ROOT,check=True)
    count=check_axioms(source,MODULE)
    claims=[
        'example : 2^5 * Collatz.acceleratedOrbit 5 16 ≤ 3*(16+5) := by decide\n',
        'example : 28*4^0 < 10*8^0 := by decide\n',
        'example : 79 ≤ Collatz.orbit 13 79 := by decide\n',
    ]
    rejected=check_false_certificates(MODULE,claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__=='__main__':
    main()
