#!/usr/bin/env python3
"""Audit endpoint reduction and independently reproduce gap-cutoff records."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations

def main():
    name='Collatz.Exploration.GapTenThousand'
    source=ROOT/'Collatz/Exploration/GapTenThousand.lean'
    for part in ['GapEndpointCertificates','GapEndpointScan','GapTenThousand']:
        assert not violations((ROOT/f'Collatz/Exploration/{part}.lean').read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    C=1;A=0;record=0;records=[];pairs=0
    for j in range(1,10001):
        D=2**j
        if C*3<D:C*=3;A+=1
        assert C<D<=C*3
        bound=A*C//(3*(D-C))+1
        assert A*C<3*(D-C)*bound
        if bound>record:
            record=bound;records.append((j,A,bound))
        if j<=128:
            for a in range(A+1):
                assert a*3**a<3*(D-3**a)*bound
                pairs+=1
    assert record==3330950 and records[-1]==(9971,6291,3330950)
    assert (65,41,1186) in records
    axioms=sum(check_axioms(ROOT/f'Collatz/Exploration/{part}.lean',f'Collatz.Exploration.{part}') for part in ['GapEndpointCertificates','GapEndpointScan','GapTenThousand'])
    bad=check_false_certificates(name,[
        'set_option maxRecDepth 200000 in\nset_option maxHeartbeats 0 in\nexample : Collatz.Exploration.GapEndpointScan.scan 1185 65 0 1 1 = true := by decide\n',
        'set_option maxRecDepth 200000 in\nset_option maxHeartbeats 0 in\nexample : Collatz.Exploration.GapEndpointScan.scan 3330949 10000 0 1 1 = true := by decide\n',
    ])
    print(f'10000 independently computed endpoints; {pairs} lower-odd-count controls; {axioms} theorem footprints; {bad} false controls')
    print('The full horizon certificate is now checked by Lean; no crossing existence is proved.')

if __name__=='__main__':main()
