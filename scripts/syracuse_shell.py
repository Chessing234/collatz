#!/usr/bin/env python3
"""Exact counts of valuation words of length n and total 2n, modulo 3**n.

All words in this group have probability 4**(-n). Counting them together
tests a collective lower-bound route; it does not prove a bound at all n.
The range cap keeps both modular products and counts inside integer limits.
"""

import argparse
from math import comb

import numpy as np


def report(depth):
    if not 1 <= depth <= 15:
        raise ValueError('depth must be in 1..15')
    previous = {0: np.array([1], dtype=np.uint64)}
    print(' n   missing units   total units   min count   count at 1   max count')
    for n in range(1, depth + 1):
        modulus = 3 ** n
        base = 3 * np.arange(modulus // 3, dtype=np.int64) + 1
        totals = [2 * depth] if n == depth else range(n, depth + n + 1)
        current = {s: np.zeros(modulus, dtype=np.uint64) for s in totals}
        for v in range(1, depth + 2):
            indices = base * pow(2, -v, modulus) % modulus
            for s in totals:
                if s - v in previous:
                    current[s][indices] += previous[s - v]
        counts = current[2 * n]
        units = np.arange(modulus) % 3 != 0
        assert int(counts.sum()) == comb(2 * n - 1, n - 1)
        print(f'{n:2d} {int((counts[units] == 0).sum()):15d} '
              f'{int(units.sum()):13d} {int(counts[units].min()):11d} '
              f'{int(counts[1]):12d} {int(counts.max()):11d}')
        previous = current


def check_159():
    value = 159
    valuations = []
    while value != 1:
        numerator = 3 * value + 1
        v = (numerator & -numerator).bit_length() - 1
        valuations.append(v)
        value = numerator >> v
    assert len(valuations) == 18 and sum(valuations) == 36
    modulus = 3 ** 18
    offset = 0
    for v in valuations:
        offset = (3 * offset + 1) * pow(2, -v, modulus) % modulus
    assert offset == 1
    assert valuations != [2] * 18
    return valuations


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=12)
    args = parser.parse_args()
    report(args.depth)
    print('Additional depth-18 word at residue 1 (reverse this forward list):', check_159())
