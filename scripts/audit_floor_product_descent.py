#!/usr/bin/env python3
"""Kernel and independent finite descent-certificate tests."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

def main():
    name='Collatz.Exploration.FloorProductDescent'
    source=ROOT/'Collatz/Exploration/FloorProductDescent.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    checked=certified=0
    for n in range(1,2001):
        v=3*(n+1 if n%2==0 else n);w=v+1
        x=n; C=D=1; a=0; descended=False
        for j in range(101):
            if C*w**a<D*v**a:
                assert descended
                certified+=1
            checked+=1
            if x%2: x=(3*x+1)//2;C*=3;a+=1
            else:x//=2
            D*=2
            descended |= x<n
    assert certified>0
    missing=delayed=matched=0
    maxgap=(0,0,0,0)
    for n in range(2,2001):
        v=3*(n+1 if n%2==0 else n);w=v+1
        x=n;C=D=1;a=0;first_desc=first_cert=None
        for j in range(201):
            if x<n and first_desc is None:first_desc=j
            if C*w**a<D*v**a and first_cert is None:first_cert=j
            if x%2:x=(3*x+1)//2;C*=3;a+=1
            else:x//=2
            D*=2
        if first_cert is None:missing+=1
        else:
            assert first_desc is not None and first_desc<=first_cert
            gap=first_cert-first_desc
            matched+=gap==0;delayed+=gap>0
            maxgap=max(maxgap,(gap,n,first_desc,first_cert))
    print(f'First-certificate comparison through 200: {matched} exact; {delayed} delayed; {missing} missing; max gap {maxgap}')
    axioms=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : 3^1*4^1 < 2^1*3^1 := by decide\n',
        'example : Collatz.acceleratedOrbit 0 4 < 4 := by decide\n',
    ])
    print(f'{checked} horizons; {certified} valid descent certificates; {axioms} theorem footprints; {bad} false controls')

if __name__=='__main__':main()
