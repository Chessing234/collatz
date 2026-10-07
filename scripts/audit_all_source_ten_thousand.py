#!/usr/bin/env python3
"""Check the all-source conditional theorem and reproduce the finite census."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations


def first_crossing(n, horizon):
    x=n; C=D=1
    for j in range(horizon+1):
        if C<D:
            return j, x
        if x%2:
            x=(3*x+1)//2
            C*=3
        else:
            x//=2
        D*=2
    return None


def main():
    parts=['BalancedFirstLightScan', 'AllSourceTenThousand']
    for part in parts:
        assert not violations((ROOT/f'Collatz/Exploration/{part}.lean').read_text())
    latest=(0,0)
    for n in range(2,3330950):
        result=first_crossing(n,256)
        assert result is not None and result[1]<n, (n,result)
        if result[0]>latest[1]:
            latest=(n,result[0])
    assert latest==(1126015,224), latest
    name='Collatz.Exploration.AllSourceTenThousand'
    subprocess.run(['lake','build','Collatz.Exploration.BalancedFirstLightScan'],cwd=ROOT,check=True)
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    footprints=sum(check_axioms(ROOT/f'Collatz/Exploration/{part}.lean',
        f'Collatz.Exploration.{part}') for part in parts)
    false=check_false_certificates('Collatz.Exploration.BalancedFirstLightScan',[
        'example : Collatz.Exploration.BalancedFirstLightScan.checkTree 1 2 3 1 = true := by decide\n',
        'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\nexample : Collatz.FirstLightScan.check 223 1126015 = true := by decide\n',
    ])
    print(f'3330948 independently checked sources; latest crossing {latest}; '
          f'{footprints} theorem footprints; {false} false controls')
    print('First crossing by 10000 implies descent for every n>1; crossing existence remains open.')


if __name__=='__main__':
    main()
