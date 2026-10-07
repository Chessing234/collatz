#!/usr/bin/env python3
"""Check finite-prefix Beatty barriers with an independent exact-orbit census."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations


def main():
    source=ROOT/'Collatz/Exploration/FiniteBeattyBarrier.lean'
    assert not violations(source.read_text())
    b=[0]; f=[]; cutoff=1
    for a in range(64):
        f.append((3**a).bit_length()-1)
        cutoff=max(cutoff,b[a]//(2**(f[a]+1)-3**a)+1)
        b.append(3*b[a]+2**f[a])
    assert cutoff==868
    checks=0
    for n in range(cutoff,100001):
        x=n; a=B=0
        for j in range(257):
            if x<n:
                break
            assert 2**j*x==3**a*n+B
            if a<=64:
                assert B<=b[a], (n,j,a,B,b[a])
                if a<64:
                    assert j<=f[a], (n,j,a)
                checks+=1
            if x%2:
                x=(3*x+1)//2; a+=1; B=3*B+2**j
            else:
                x//=2
    assert checks==344004, checks
    name='Collatz.Exploration.FiniteBeattyBarrier'
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    footprints=check_axioms(source,name)
    false=check_false_certificates(name,[
        'example : Collatz.AffineExact.affineC 2 2 <= Collatz.RealizableBound.Bcap (Collatz.oddCount 2 2) := by decide\n',
        'example : 2 <= Collatz.RealizableBound.fexp (Collatz.oddCount 2 2) := by decide\n',
    ])
    print(f'{checks} exact non-descent prefixes; {footprints} theorem footprints; {false} false controls')
    print('The finite non-descent and odd-count-reach hypotheses remain essential.')


if __name__=='__main__':
    main()
