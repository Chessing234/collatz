#!/usr/bin/env python3
"""Audit the cofactor-free one-step drop threshold."""
import math
import re
import subprocess
from audit_barrier_kernel import ROOT, lean_check, check_false_certificates
from check_proof_escapes import violations


def excursion(n):
    x = n
    v = 0
    while x % 2:
        x = (3 * x + 1) // 2
        v += 1
    w = 0
    while x % 2 == 0:
        x //= 2
        w += 1
    return v, w, x


def census():
    comparisons = heavy = heavy_long = 0
    for v in range(1, 9):
        for w in range(1, v + 5):
            bound = 3 ** v <= (1 << w) * ((1 << v) - 1)
            for u in range(1, 301, 2):
                holds = 3 ** v * u + (1 << w) <= (1 << (v + w)) * u
                if bound:
                    assert holds
                if u == 1:
                    assert holds == bound
                comparisons += 1
            if bound and v >= 4:
                heavy_long += 1
    caught = 0
    for n in range(3, 20001, 2):
        v, w, landing = excursion(n)
        if 3 ** v <= (1 << w) * ((1 << v) - 1):
            assert landing < n
            heavy += 1
            if v >= 4:
                caught += 1
    gaps = []
    for v in range(2, 41):
        three = 3 ** v
        for w in range(1, v + 6):
            if (1 << w) * ((1 << v) - 1) < three < (1 << (v + w)):
                gaps.append((v, w))
    assert not gaps
    margin = 0
    for v in range(3, 41):
        w = v - v // 3
        assert 3 ** v <= (1 << w) * ((1 << v) - 1)
        margin += 1
    sharp = 0
    met = 0
    for v in range(2, 971):
        w = v - (127 * v) // 306
        assert 3 ** v <= (1 << w) * ((1 << v) - 1)
        sharp += 1
        boundary = (3 ** v).bit_length() - v
        if w <= boundary:
            met += 1
    assert met == 969
    shared = 0
    for v in range(2, 401):
        three = 3 ** v
        k = three.bit_length()
        if math.gcd(v, k) >= 2:
            shared += 1
            assert (1 << k) - three >= 1 << (k - v)
    assert shared > 0
    jumps = 0
    prev = (3 ** 1).bit_length()
    for v in range(2, 401):
        three = 3 ** v
        k = three.bit_length()
        if k == prev + 2:
            jumps += 1
            assert (1 << k) - three >= 1 << (k - v)
        prev = k
    assert jumps > 0
    ks = [(3 ** v).bit_length() for v in range(1, 402)]
    isolated = 0
    for v in range(2, 401):
        step = ks[v - 1] - ks[v - 2]
        assert step in (1, 2)
        if step == 1:
            isolated += 1
            assert ks[v] - ks[v - 1] == 2
            if v >= 3:
                assert ks[v - 2] - ks[v - 3] == 2
    assert isolated > 0
    return (comparisons, heavy, caught, heavy_long, margin, sharp, met,
            shared, jumps, isolated)


def check_heavy_axioms(source):
    names = re.findall(r'^theorem (\w+)', source.read_text(), re.MULTILINE)
    assert names
    module = 'Collatz.Strategy.ExcursionHeavy'
    namespace = 'Collatz.ExcursionHeavy'
    audit = lean_check(''.join(f'#print axioms {namespace}.{name}\n' for name in names),
                        module)
    assert audit.returncode == 0, audit.stdout + audit.stderr
    footprints = re.findall(
        rf"'{re.escape(namespace)}\.(\w+)' "
        r'(?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])',
        audit.stdout)
    assert [name for name, _ in footprints] == names, audit.stdout
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in footprints:
        found = {axiom.strip() for axiom in axioms.split(',') if axiom.strip()}
        assert found <= allowed, (name, found)
        assert 'sorryAx' not in found
    return len(names)


def main():
    heavy = ROOT / 'Collatz/Strategy/ExcursionHeavy.lean'
    chain = ROOT / 'Collatz/Strategy/ExcursionChain.lean'
    assert not violations(heavy.read_text())
    assert not violations(chain.read_text())
    (comparisons, heavy_n, caught, pairs, margin, sharp, met, shared, jumps,
     isolated) = census()
    subprocess.run(['lake', 'build', 'Collatz.Strategy.ExcursionChain'],
                   cwd=ROOT, check=True)
    footprints = check_heavy_axioms(heavy)
    false = check_false_certificates('Collatz.Strategy.ExcursionHeavy', [
        'example : (3 : Nat) ^ 4 ≤ 2 ^ 2 * (2 ^ 4 - 1) := by decide\n',
        'example : Collatz.acceleratedOrbit (4 + 1) 47 < 47 := by decide\n',
        'example : 2 ^ 3 * (2 ^ 5 - 1) < 3 ^ 5 ∧ 3 ^ 5 < 2 ^ (5 + 3) := by decide\n',
        'example : (3 : Nat) ^ 3 ≤ 2 ^ (3 - 3 / 3 - 1) * (2 ^ 3 - 1) := by decide\n',
        'example : (3 : Nat) ^ 5 ≤ 2 ^ (5 - 127 * 5 / 306 - 1) * (2 ^ 5 - 1) := by decide\n',
        'example : 2 ≤ Nat.gcd 5 (Collatz.ExcursionHeavy.twoCeil (3 ^ 5)) := by decide\n',
        'example : Collatz.ExcursionHeavy.twoCeil (3 ^ (5 - 1)) + 2 = Collatz.ExcursionHeavy.twoCeil (3 ^ 5) := by decide\n',
        'example : Collatz.ExcursionHeavy.twoCeil (3 ^ (5 + 1)) = Collatz.ExcursionHeavy.twoCeil (3 ^ 5) + 1 := by decide\n',
    ])
    print(f'{comparisons} cofactor comparisons; {heavy_n} heavy odd starts '
          f'below 20000, {caught} of them with run length at least 4; '
          f'{pairs} heavy pairs with v≥4 in the scanned range')
    print(f'{footprints} theorem footprints; {false} false controls')
    print('No gap between the threshold and one-step failure was found '
          'for run lengths 2 through 40. The scan agrees with the proof '
          'through run length 128 and for every even pair; it is not itself '
          'a proof.')
    print(f'For all {margin} run lengths from 3 through 40, '
          'W ≥ v − ⌊v/3⌋ meets the threshold. That inequality is proved '
          'for every v ≥ 3; the scan is not that proof.')
    print(f'For all {sharp} run lengths from 2 through 970, '
          f'W ≥ v − ⌊127v/306⌋ meets the threshold. That inequality is '
          'proved for every v ≥ 2; the scan is not that proof.')
    print(f'On those {met} lengths the cutoff is at most the boundary '
          'count. That comparison is a scan, not a proof. The kernel check '
          'of the boundary stops at 128.')
    print('Past length 970 the boundary can sit below this cutoff. '
          'Light runs, including every (v, W) = (v, 1) with v≥2, remain open.')
    print(f'For all {shared} lengths from 2 through 400 whose binary '
          'ceiling shares a factor with the length, the boundary defect '
          'is at least one. That inequality is proved for every such '
          'length; the scan is not that proof. Coprime ceilings are not '
          'covered.')
    print(f'For all {jumps} lengths from 2 through 400 whose binary '
          'ceiling grew by two, the boundary defect is at least one. '
          'That inequality is proved for every such length; the scan is '
          'not that proof. A ceiling that grows by one is not covered.')
    print(f'For all lengths from 2 through 400 the binary ceiling grows '
          f'by one or two. All {isolated} growths of one are isolated '
          'between growths of two. That pattern is proved for every '
          'length; the scan is not that proof. An isolated growth past '
          '128, coprime to its ceiling, is still open.')


if __name__ == '__main__':
    main()
