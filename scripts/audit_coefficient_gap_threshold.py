#!/usr/bin/env python3
"""Exact scalar-to-product and conditional descent audit."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

def main():
    name='Collatz.Exploration.CoefficientGapThreshold'
    source=ROOT/'Collatz/Exploration/CoefficientGapThreshold.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    tested=certified=0
    for C in range(11):
        for D in range(11):
            for k in range(21):
                for b in range(21):
                    v=3*(b+1 if b%2==0 else b);w=v+1
                    if C*w<D*max(w-k,0):assert C*w**k<D*v**k
                    if C<=D and k*D<(D-C)*w:
                        assert C*w<D*max(w-k,0)
                        assert C*w**k<D*v**k
                        certified+=1
                    tested+=1
    orbit_cases=0
    for n in range(1,2001):
        x=n;C=D=1;a=0;desc=False
        w=3*(n+1 if n%2==0 else n)+1
        for j in range(101):
            if C<=D and a*D<(D-C)*w:
                assert desc;orbit_cases+=1
            odd=x%2;a+=odd
            x=(3*x+1)//2 if odd else x//2
            C*=3 if odd else 1;D*=2
            desc |= x<n
    cutoff_cases=0
    for H in range(1,33):
        cutoff=H*2**H//3+1
        for n in range(cutoff,cutoff+100):
            x=n;C=D=1
            for j in range(1,H+1):
                odd=x%2
                x=(3*x+1)//2 if odd else x//2
                C*=3 if odd else 1;D*=2
                if C<D:
                    assert H*2**H<3*n and x<n
                    cutoff_cases+=1
                    break
    print(f'{cutoff_cases} first-light cutoff cases')
    axioms=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : 3*4 < 2*(4-1) := by decide\n',
        'example : 41*2^65 < (2^65-3^41)*4 := by decide\n',
    ])
    print(f'{tested} scalar cases; {certified} valid scalar certificates; {orbit_cases} descent cases; {axioms} theorem footprints; {bad} false controls')

if __name__=='__main__':main()
