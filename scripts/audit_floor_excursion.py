#!/usr/bin/env python3
"""Build and audit the floor excursion theorem and its sharpness statements."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates

MODULE = 'Collatz.Exploration.FloorExcursion'


def main():
    subprocess.run(['lake', 'build', MODULE], cwd=ROOT, check=True)
    subprocess.run(['python3', str(ROOT / 'scripts/test_floor_excursion.py')],
                   cwd=ROOT, check=True)
    count = check_axioms(ROOT / 'Collatz/Exploration/FloorExcursion.lean', MODULE)
    false_claims = [
        'example : 16*Collatz.orbit 8 27 = 81*27+86 := by decide\n',
        'example : Collatz.Exploration.BarrierKernel.intervalCheck 27 135 8 27 = true := by decide\n',
        'example : (List.range 8).any (fun k => decide (81*27+85 ≤ 16*Collatz.orbit k 27)) = true := by decide\n',
        'example : (List.range 9).any (fun k => decide (81*1+85 ≤ 16*Collatz.orbit k 1)) = true := by decide\n',
    ]
    rejected = check_false_certificates(MODULE, false_claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__ == '__main__':
    main()
