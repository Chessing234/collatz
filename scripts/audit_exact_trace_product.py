#!/usr/bin/env python3
"""Exact trace-product kernel and independent recurrence audit."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

def main():
    name='Collatz.Exploration.ExactTraceProduct'
    source=ROOT/'Collatz/Exploration/ExactTraceProduct.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    checks=0
    for n in range(1001):
        x=n; A=Z=C=D=1
        for j in range(61):
            assert A*D*x==Z*C*n
            if n > 0: assert (x<n)==(Z*C<A*D)
            checks+=1
            if x%2:
                A*=3*x; Z*=3*x+1; C*=3; x=(3*x+1)//2
            else: x//=2
            D*=2
    count=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : Collatz.Exploration.ExactTraceProduct.numerator 3 1 = 10 := by decide\n',
        'example : Collatz.Exploration.ExactTraceProduct.denominator 3 1 = 9 := by decide\n',
    ])
    print(f'{checks} identities; {count} theorem footprints; {bad} false controls rejected')

if __name__=='__main__':main()
