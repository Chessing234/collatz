#!/usr/bin/env python3
"""Kernel and exact threshold monotonicity checks."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

def passes(C,D,k,b):
    v=3*(b+1 if b%2==0 else b)
    return C*(v+1)**k<D*v**k

def main():
    name='Collatz.Exploration.ProductThresholds'
    source=ROOT/'Collatz/Exploration/ProductThresholds.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    checks=0
    for C,D,k in [(3**41,2**65,41),(3**37,2**59,37),(1,1,0),(1,2,0),(3,2,1),(243,256,5)]:
        seen=False
        for b in range(2001):
            p=passes(C,D,k,b)
            assert not seen or p
            seen |= p
            if (C,D,k)==(3**41,2**65,41):assert p==(b>=1192)
            if (C,D,k)==(3**37,2**59,37):assert p==(b>=50)
            checks+=1
    class_cases=0
    for n in range(2,50001):
        x=n;a=0;desc=False
        for j in range(1,66):
            odd=x%2;a+=odd
            x=(3*x+1)//2 if odd else x//2
            desc |= x<n
            if (j==59 and a==37 and n>=50) or (j==65 and a==41 and n>=1192):
                assert desc
                class_cases+=1
    assert class_cases>0
    print(f'{class_cases} matching odd-count descent cases')
    axioms=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : Collatz.Exploration.ProductThresholds.Passes (3^41) (2^65) 41 1191 := by decide\n',
        'example : Collatz.Exploration.ProductThresholds.Passes (3^37) (2^59) 37 49 := by decide\n',
    ])
    print(f'{checks} exact threshold checks; {axioms} theorem footprints; {bad} false controls')

if __name__=='__main__':main()
