#!/usr/bin/env python3
"""Independent finite count comparisons and cutoff rounding controls."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

def flags(n,H):
    x=n;C=D=1;actual=heavy=True
    for j in range(H):
        odd=x%2;x=(3*x+1)//2 if odd else x//2
        C*=3 if odd else 1;D*=2
        actual &= x>=n;heavy &= C>=D
    return actual,heavy

def main():
    name='Collatz.Exploration.SharpSurvivalCounts'
    source=ROOT/'Collatz/Exploration/SharpSurvivalCounts.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    checks=0
    for H in range(13):
        cutoff=max(H*2**H//3-1,0)
        heavy_count=sum(flags(r,H)[1] for r in range(2**H))
        actual=periodic=0
        for N in range(3001):
            if N:
                a,p=flags(N+1,H);actual+=a;periodic+=p
            assert actual<=cutoff+periodic
            assert periodic<=cutoff+actual
            assert actual<=cutoff+(N//2**H+1)*heavy_count
            checks+=1
        for n in range(cutoff,cutoff+20):
            assert H*2**H<3*(n+2)
            a,p=flags(n+2,H);assert a==p
    axioms=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'example : Collatz.Exploration.SharpSurvivalCounts.cutoff 3 = 8 := by decide\n',
        'example : Collatz.Exploration.SharpSurvivalCounts.cutoff 8 = 682 := by decide\n',
    ])
    print(f'{checks} count cutoffs; {axioms} theorem footprints; {bad} false rounding controls')

if __name__=='__main__':main()
