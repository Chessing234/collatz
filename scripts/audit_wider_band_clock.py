#!/usr/bin/env python3
"""Reproduce and audit sharp seventeen-step clocks and generic witness transfer."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations

MODULES = ['BandClock', 'WiderBandArithmetic', 'WiderBandClock']
PREFIX = 'Collatz.Exploration.'


def main():
    subprocess.run(['python3', str(ROOT / 'scripts/generate_wider_band_arithmetic.py')],
                   cwd=ROOT, check=True)
    for name in MODULES:
        assert not violations((ROOT / f'Collatz/Exploration/{name}.lean').read_text())
    subprocess.run(['lake', 'build', PREFIX+'WiderBandClock'], cwd=ROOT, check=True)
    subprocess.run(['python3', str(ROOT / 'scripts/test_wider_band_clock.py')],
                   cwd=ROOT, check=True)
    count = sum(check_axioms(ROOT / f'Collatz/Exploration/{name}.lean', PREFIX+name)
                for name in MODULES)
    barrier = PREFIX+'BarrierKernel.intervalCheck'
    claims = [
        f'example : {barrier} 379 (21*379/4) 16 1010 = false := by decide\n',
        'example : Collatz.orbit 17 1010 = 362 := by decide\n',
        f'example : {barrier} 1 (21/4) 17 1 = false := by decide\n',
        'example : (List.range 18).any (fun k => decide (21*2 < 4*Collatz.orbit k 2)) = true := by decide\n',
    ]
    rejected = check_false_certificates(PREFIX+'WiderBandClock', claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__ == '__main__':
    main()
