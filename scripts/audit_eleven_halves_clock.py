#!/usr/bin/env python3
"""Reproduce and audit sharp thirty-step ratio-11/2 clock."""
import subprocess
from audit_barrier_kernel import ROOT, check_axioms, check_false_certificates
from check_proof_escapes import violations

MODULES = ['BandClock', 'ElevenHalvesArithmetic', 'ElevenHalvesClock', 'ElevenHalvesFamily']
PREFIX = 'Collatz.Exploration.'


def main():
    subprocess.run(['python3', str(ROOT / 'scripts/generate_wider_band_arithmetic.py'),
                    '--numerator','11','--denominator','2','--horizon','30',
                    '--module','ElevenHalvesArithmetic','--leaves','235','--split-lines','1200','--prune-context'],
                   cwd=ROOT, check=True)
    parts=sorted((ROOT/'Collatz/Exploration/ElevenHalvesArithmetic').glob('Part*.lean'))
    for path in parts:
        assert not violations(path.read_text())
    for name in MODULES:
        assert not violations((ROOT / f'Collatz/Exploration/{name}.lean').read_text())
    subprocess.run(['lake', 'build', PREFIX+'ElevenHalvesFamily'], cwd=ROOT, check=True)
    subprocess.run(['python3', str(ROOT / 'scripts/test_eleven_halves_clock.py')],
                   cwd=ROOT, check=True)
    count = sum(check_axioms(ROOT / f'Collatz/Exploration/{name}.lean', PREFIX+name)
                for name in MODULES)
    count += sum(check_axioms(path,PREFIX+'ElevenHalvesArithmetic') for path in parts)
    barrier = PREFIX+'BarrierKernel.intervalCheck'
    family = PREFIX+'ElevenHalvesFamily'
    claims = [
        f'example : Collatz.orbit 30 ({family}.source 1) < {family}.barrier 1 := by decide\n',
        f'example : 11*{family}.barrier 0 < 2*Collatz.orbit 30 ({family}.source 0) := by decide\n',
        f'example : {barrier} 71803 (11*71803/2) 29 201714 = false := by decide\n',
        'example : Collatz.orbit 30 201714 = 68159 := by decide\n',
        f'example : {barrier} 1 (11/2) 30 1 = false := by decide\n',
        'example : (List.range 31).any (fun k => decide (11*2 < 2*Collatz.orbit k 2)) = true := by decide\n',
    ]
    rejected = check_false_certificates(PREFIX+'ElevenHalvesFamily', claims)
    print(f'{count} theorem axiom footprints checked; {rejected} false claims rejected')


if __name__ == '__main__':
    main()
