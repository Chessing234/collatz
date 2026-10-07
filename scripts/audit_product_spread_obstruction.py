#!/usr/bin/env python3
"""Kernel audit and exact coefficient-corridor obstruction checks."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations
from test_six_band_prefixes import balanced_residue

def main():
    name='Collatz.Exploration.ProductSpreadObstruction'
    source=ROOT/'Collatz/Exploration/ProductSpreadObstruction.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    pairs=0
    for K in [16,64,256,1024]:
        _,bits=balanced_residue(K)
        C,D=1,1
        coeffs=[(C,D)]
        for bit in bits:
            C*=3 if bit else 1; D*=2
            assert D<=C<3*D
            coeffs.append((C,D))
        for L,D in coeffs:
            for H,E in coeffs:
                assert H*D<=3*E*L
                pairs+=1
    checked=0
    for b in range(31):
        v=3*(b+1 if b%2==0 else b);w=v+1
        for k in range(31):
            for A in range(31):
                for Z in range(A,31):
                    assert A*v**k<=Z*w**k
                    checked+=1
    count=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : 4*1 ≤ 3*1*1 := by decide\n',
        'example : 4*4^1 ≤ 3*3^1 := by decide\n',
    ])
    print(f'{pairs} corridor pairs; {checked} product controls; {count} theorem footprints; {bad} false claims rejected')

if __name__=='__main__': main()
