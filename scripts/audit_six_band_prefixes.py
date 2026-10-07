#!/usr/bin/env python3
"""Audit arbitrarily long bounded-ratio prefixes and reject false transfers."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

NAMES=['BalancedResidue','SixBandPrefixes']
PREFIX='Collatz.Exploration.'


def main():
    for name in NAMES:
        assert not violations((ROOT/f'Collatz/Exploration/{name}.lean').read_text())
    subprocess.run(['lake','build',PREFIX+'SixBandPrefixes'],cwd=ROOT,check=True)
    subprocess.run(['python3',str(ROOT/'scripts/test_six_band_prefixes.py')],cwd=ROOT,check=True)
    count=sum(check_axioms(ROOT/f'Collatz/Exploration/{name}.lean',PREFIX+name) for name in NAMES)
    claims=[
        'example : Collatz.orbit 1 3 ≤ 5 := by decide\n',
        'example : 3 ≤ Collatz.orbit 6 3 := by decide\n',
        'example : 2*10+11 < 3*10 := by decide\n',
        'example : Collatz.orbit 1 (2^128*100) ≥ 2^128*100 := by decide\n',
    ]
    rejected=check_false_certificates(PREFIX+'SixBandPrefixes',claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__=='__main__':
    main()
