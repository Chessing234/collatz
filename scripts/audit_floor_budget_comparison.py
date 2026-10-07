#!/usr/bin/env python3
"""Audit classical Bernoulli comparison for finite-floor error budgets."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations

def main():
    name='Collatz.Exploration.FloorBudgetComparison'
    source=ROOT/'Collatz/Exploration/FloorBudgetComparison.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    count=0
    for v in range(101):
        w=v+1
        for k in range(201):
            assert w**(k+1)<=w*v**k+k*w**k
            assert max(w-k,0)*w**k<=w*v**k
            if k<=w:
                assert (w-k)*(w**k-v**k)<=k*v**k
            count+=1
    axioms=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : 4^3 ≤ 4*3^2+1*4^2 := by decide\n',
        'example : (4-2)*(4^2-3^2) ≤ 1*3^2 := by decide\n',
    ])
    print(f'{count} exact comparisons; {axioms} theorem footprints; {bad} false controls rejected')

if __name__=='__main__': main()
