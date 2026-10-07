#!/usr/bin/env python3
"""Audit the universal twelve-step clock and conditional high-visit witnesses."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates

MODULE = 'Collatz.Exploration.FiveBandClock'


def main():
    subprocess.run(['python3', str(ROOT / 'scripts/generate_five_band_arithmetic.py')],
                   cwd=ROOT, check=True)
    subprocess.run(['lake', 'build', MODULE], cwd=ROOT, check=True)
    subprocess.run(['python3', str(ROOT / 'scripts/test_five_band_clock.py')],
                   cwd=ROOT, check=True)
    count = check_axioms(ROOT / 'Collatz/Exploration/FiveBandClock.lean', MODULE)
    count += check_axioms(ROOT / 'Collatz/Exploration/FiveBandArithmetic.lean',
                          'Collatz.Exploration.FiveBandArithmetic')
    false_claims = [
        'example : Collatz.Exploration.BarrierKernel.intervalCheck 40 200 11 114 = false := by decide\n',
        'example : Collatz.Exploration.BarrierKernel.intervalCheck 1 5 12 1 = false := by decide\n',
        'example : Collatz.orbit 12 114 = 38 := by decide\n',
        'example : (List.range 13).any (fun k => decide (10 < Collatz.orbit k 2)) = true := by decide\n',
    ]
    rejected = check_false_certificates(MODULE, false_claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__ == '__main__':
    main()
