#!/usr/bin/env python3
"""Build, audit every new theorem, and reject false offset/quantifier transfers."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations

MODULE = 'Collatz.Exploration.BalancedOffset'


def main():
    source=ROOT/'Collatz/Exploration/BalancedOffset.lean'
    compact=ROOT/'Collatz/Exploration/BalancedCompact.lean'
    assert not violations(source.read_text())
    assert not violations(compact.read_text())
    subprocess.run(['lake','build','Collatz.Exploration.BalancedCompact'],cwd=ROOT,check=True)
    subprocess.run(['python3',str(ROOT/'scripts/test_balanced_offset.py')],cwd=ROOT,check=True)
    count=check_axioms(source,MODULE)+check_axioms(compact,'Collatz.Exploration.BalancedCompact')
    claims=[
        'example : 2^5 * Collatz.acceleratedOrbit 5 16 ≤ 3*(16+5) := by decide\n',
        'example : 28*4^0 < 10*8^0 := by decide\n',
        'example : 79 ≤ Collatz.orbit 13 79 := by decide\n',
    ]
    rejected=check_false_certificates(MODULE,claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__=='__main__':
    main()
