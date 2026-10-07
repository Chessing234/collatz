#!/usr/bin/env python3
"""Independent paired orbit tests above the improved finite cutoff."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

def events(n,H):
    x=n;C=D=1;cross=drop=None
    for j in range(1,H+1):
        odd=x%2;x=(3*x+1)//2 if odd else x//2
        C*=3 if odd else 1;D*=2
        if C<D and cross is None:cross=j
        if x<n and drop is None:drop=j
    return cross,drop

def main():
    name='Collatz.Exploration.SharpFirstLightEventual'
    source=ROOT/'Collatz/Exploration/SharpFirstLightEventual.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    pairs=0
    for H in range(41):
        cutoff=H*2**H//3+1
        for offset in range(50):
            n=cutoff+offset;m=n+2**H
            assert H*2**H<3*n and H*2**H<3*m
            left,right=events(n,H),events(m,H)
            assert left[0]==left[1] and right[0]==right[1]
            assert left==right
            pairs+=1
    axioms=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : Collatz.FirstLightCounting.heavyCheck 2 1 = true := by decide\n',
        'example : Collatz.acceleratedOrbit 8 7 < 7 := by decide\n',
    ])
    print(f'{pairs} paired residue checks; {axioms} theorem footprints; {bad} false controls')

if __name__=='__main__':main()
