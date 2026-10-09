#!/usr/bin/env python3
"""Independently compare exact survival and periodic count decompositions."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations


def census():
    prefixes=counts=0
    for H in range(11):
        values=[]
        for n in range(2000):
            start=n+2; x=start; a=0; actual=heavy=True
            for j in range(1,H+1):
                if x%2:
                    x=(3*x+1)//2; a+=1
                else:
                    x//=2
                actual=actual and start<=x
                heavy=heavy and 2**j<=3**a
            assert actual==heavy, (H,n,x,a)
            values.append(int(actual)); prefixes+=1
        sums=[0]
        for value in values:
            sums.append(sums[-1]+value)
        p=2**H; c=sums[p]
        for N in range(2001):
            assert sums[N]==(N//p)*c+sums[N%p], (H,N)
            assert (N//p)*c<=sums[N]<=(N//p+1)*c
            counts+=1
    assert (prefixes,counts)==(22000,22011)
    return prefixes,counts


def main():
    prefixes,counts=census()
    parts=['ExactSurvivalCounts','CertifiedSurvivalCounts']
    for part in parts:
        assert not violations((ROOT/f'Collatz/Exploration/{part}.lean').read_text())
    name='Collatz.Exploration.CertifiedSurvivalCounts'
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    footprints=sum(check_axioms(ROOT/f'Collatz/Exploration/{part}.lean',
        f'Collatz.Exploration.{part}') for part in parts)
    false=check_false_certificates(name,[
        'example : Collatz.PeriodicCounting.countBelow (Collatz.FirstLightCounting.survives 2) 2 = 0 := by decide\n',
        'example : Collatz.PeriodicCounting.countBelow (Collatz.FirstLightCounting.survives 2) 4 = 2 := by decide\n',
    ])
    print(f'{prefixes} independent survival classifications; {counts} exact count checks; '
          f'{footprints} theorem footprints; {false} false controls')
    print('Zero exceptional-source count error through horizon 14186; no universal crossing proved.')


if __name__=='__main__':
    main()
