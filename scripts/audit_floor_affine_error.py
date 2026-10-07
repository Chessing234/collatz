#!/usr/bin/env python3
"""Kernel build, theorem footprints, seed reproduction, and false-transfer controls."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

NAMES=['FloorAffineError','AffineBandExit']
PREFIX='Collatz.Exploration.'


def main():
    for name in NAMES:
        assert not violations((ROOT/f'Collatz/Exploration/{name}.lean').read_text())
    subprocess.run(['lake','build',PREFIX+'AffineBandExit'],cwd=ROOT,check=True)
    subprocess.run(['python3',str(ROOT/'scripts/test_floor_affine_error.py')],cwd=ROOT,check=True)
    count=sum(check_axioms(ROOT/f'Collatz/Exploration/{name}.lean',PREFIX+name) for name in NAMES)
    bad=[
        'example : Collatz.Exploration.FloorAffineError.weight 2 = 7 := by decide\n',
        'example : 11*1 ≤ 1*(3*3+1) := by decide\n',
        'example : Collatz.Exploration.FloorAffineError.oddCeil 0 = 0 := by decide\n',
    ]
    rejected=check_false_certificates(PREFIX+'AffineBandExit',bad)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__=='__main__':
    main()
