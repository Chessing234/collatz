#!/usr/bin/env python3
"""Kernel and numerical audit of the multiplicative floor-error bound."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations

def main():
    name = 'Collatz.Exploration.FloorProductError'
    source = ROOT/'Collatz/Exploration/FloorProductError.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    subprocess.run(['python3',str(ROOT/'scripts/test_floor_product_error.py')],cwd=ROOT,check=True)
    count = check_axioms(source,name)
    rejected = check_false_certificates(name,[
        'example : 4*10 ≤ 3*4*3 := by decide\n',
        'example : Collatz.Exploration.FloorProductError.base 2 = 6 := by decide\n',
    ])
    print(f'{count} theorem footprints checked; {rejected} false claims rejected')

if __name__ == '__main__': main()
