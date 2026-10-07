#!/usr/bin/env python3
"""Audit the all-source finite crossing horizons without assuming existence."""
import subprocess
from audit_all_source_ten_thousand import first_crossing
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations


def main():
    parts=['BalancedFirstLightScan','AllSourceTenThousand','CertifiedFirstCrossing']
    for part in parts:
        assert not violations((ROOT/f'Collatz/Exploration/{part}.lean').read_text())
    latest=(0,0)
    for n in range(2,3998720):
        result=first_crossing(n,256)
        assert result is not None and result[1]<n, (n,result)
        if result[0]>latest[1]:
            latest=(n,result[0])
    assert latest==(1126015,224), latest
    name='Collatz.Exploration.CertifiedFirstCrossing'
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    footprints=sum(check_axioms(ROOT/f'Collatz/Exploration/{part}.lean',
        f'Collatz.Exploration.{part}') for part in parts)
    false=check_false_certificates(name,[
        'example : Collatz.acceleratedOrbit 2 1 < 1 := by decide\n',
        'set_option maxRecDepth 200000 in\nset_option maxHeartbeats 0 in\nset_option exponentiation.threshold 20000 in\nexample : (2:Nat)^14187 < 3^8951 := by decide\n',
        'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\nexample : Collatz.FirstLightDescent.FirstLight 1126015 223 := by decide\n',
    ])
    print(f'3998718 independently checked sources; latest crossing {latest}; '
          f'{footprints} theorem footprints; {false} false controls')
    print('Exact first-crossing descent through 14186 is conditional on crossing existence.')


if __name__=='__main__':
    main()
