#!/usr/bin/env python3
"""Check the mod-four universal-descent reduction independently."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations


def main():
    source=ROOT/'Collatz/Exploration/OddResidueDescent.lean'
    assert not violations(source.read_text())
    checks=0
    for k in range(1,25001):
        n=4*k+1
        x=(3*n+1)//2
        assert x%2==0
        assert x//2<n
        checks+=1
    x=7
    for _ in range(2):
        x=(3*x+1)//2 if x%2 else x//2
    assert x==11 and x>=7
    name='Collatz.Exploration.OddResidueDescent'
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    footprints=check_axioms(source,name)
    false=check_false_certificates(name,[
        'example : Collatz.acceleratedOrbit 2 7 < 7 := by decide\n',
    ])
    print(f'{checks} one-mod-four inputs certified computationally; '
          f'{footprints} theorem footprints; {false} false controls')
    print('Convergence of the three-mod-four class is still required.')


if __name__=='__main__':
    main()
