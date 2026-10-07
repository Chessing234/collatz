#!/usr/bin/env python3
"""Verify interval capacity proofs, independent enumeration, and false controls."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates

MODULE = 'Collatz.Exploration.IntervalCapacity'
TWO_MODULE = 'Collatz.Exploration.TwoStepCapacity'


def main():
    subprocess.run(['lake', 'build', TWO_MODULE], cwd=ROOT, check=True)
    subprocess.run(['python3', str(ROOT / 'scripts/test_interval_capacity.py')],
                   cwd=ROOT, check=True)
    count = check_axioms(ROOT / 'Collatz/Exploration/IntervalCapacity.lean', MODULE)
    count_two = check_axioms(ROOT / 'Collatz/Exploration/TwoStepCapacity.lean', TWO_MODULE)
    bad = [
        f'example : {MODULE}.capacity 3 10 = 5 := by decide\n',
        f'example : {MODULE}.unrank 3 10 3 = 5 := by decide\n',
        'example : Collatz.Exploration.BarrierKernel.intervalCheck 1 2 2 2 = true := by decide\n',
    ]
    rejected = check_false_certificates(MODULE, bad)
    bad_two = [f'example : {TWO_MODULE}.capacityTwo 100 1000 = 386 := by decide\n']
    rejected += check_false_certificates(TWO_MODULE, bad_two)
    print(f'{count + count_two} theorem axiom footprints checked; {rejected} false certificates rejected')


if __name__ == '__main__':
    main()
