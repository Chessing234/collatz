"""Independent check against the original 2m-input Collatz multigraph.

This is experimental verification; no output is imported as a Lean premise.
The cut enumeration is the existing edge-deletion/bridge algorithm.
"""
import argparse
import json
from math import gcd, isqrt
from two_defect_probe import cuts_of_size_two


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def original_boundary(m, vertices):
    return sum((n % m in vertices) != (
        (n // 2 if n % 2 == 0 else (3*n+1)//2) % m in vertices)
        for n in range(2*m))


def check_set(m, vertices):
    q = len(vertices)
    D = {2*x % m for x in vertices}
    A = {(3*x+1)*pow(2, -1, m) % m for x in vertices}
    bd, ba = len(D ^ vertices), len(A ^ vertices)
    assert bd + ba == original_boundary(m, vertices)
    assert bd % 2 == ba % 2 == 0
    if bd + ba == 2:
        if A == vertices:
            assert (5*q*(q*q-1)) % m == 0
        elif D == vertices:
            assert (21*q*(q*q-1)) % m == 0
        else:
            raise AssertionError((m, sorted(vertices), 'neither branch invariant'))
        assert (105*q*(q*q-1)) % m == 0
        if is_prime(m) and m > 7:
            assert q in (1, m-1)
    if is_prime(m) and m > 7 and 2 <= q <= m-2:
        assert bd + ba >= 4


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-modulus', type=int, default=251)
    args = parser.parse_args()
    rows, subset_checks = [], 0
    for m in range(5, args.max_modulus+1, 2):
        if gcd(m, 6) != 1:
            continue
        cuts = cuts_of_size_two(m)
        for side in cuts:
            S = set(side)
            check_set(m, S)
            check_set(m, set(range(m))-S)
        if is_prime(m) and m > 7:
            assert cuts == {(0,), (m-1,)}
        # Independent exhaustive subset cross-check of edge conventions and bound.
        if m <= 19:
            for mask in range(1 << m):
                check_set(m, {x for x in range(m) if mask >> x & 1})
                subset_checks += 1
        rows.append({'modulus': m, 'prime': is_prime(m),
                     'two_edge_cut_smaller_sides': sorted(cuts)})
    print(json.dumps({'method': 'original Collatz multigraph; all two-edge cuts by bridge enumeration',
                      'max_modulus': args.max_modulus,
                      'moduli_checked': len(rows),
                      'exhaustive_small_subset_checks': subset_checks,
                      'failures': 0, 'results': rows}, indent=2))


if __name__ == '__main__':
    main()
