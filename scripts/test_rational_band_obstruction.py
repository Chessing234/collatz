#!/usr/bin/env python3
"""Exact Fraction dynamics, odd-scale encodings, and integer comparison controls."""
from fractions import Fraction as F
from itertools import combinations
from test_barrier_kernel import trajectory


def rational_step(x):
    assert x.denominator % 2 == 1
    return x/2 if x.numerator % 2 == 0 else 3*x+1


def numerator_step(d, n):
    return n//2 if n % 2 == 0 else 3*n+d


def main():
    expected = [23, 74, 37, 116, 58, 29, 92, 46]
    x = F(23, 5)
    for k in range(10000):
        assert x == F(expected[k % 8], 5)
        assert F(23, 5) <= x <= F(116, 5)
        assert x < F(81, 16)*F(23, 5)
        x = rational_step(x)
    assert x == F(23, 5)
    assert F(81, 16)*F(23, 5)-F(116, 5) == F(7, 80)
    assert F(116, 23) < F(51, 10)
    scales = list(range(1, 8192, 2)) + [2**p-1 for p in (90, 180, 512, 1024)]
    for t in scales:
        n = 23*t
        for k in range(64):
            assert n == expected[k % 8]*t
            assert F(n, 5*t) == F(expected[k % 8], 5)
            n = numerator_step(5*t, n)
        assert n == 23*t
    # Systematic enumeration of the 56 branch words with three odd updates.
    words = genuine = 0
    ratios = []
    for positions in combinations(range(8), 3):
        word = ''.join('1' if i in positions else '0' for i in range(8))
        a, c = F(1), F(0)
        for bit in word:
            a, c = (a/2, c/2) if bit == '0' else (3*a, 3*c+1)
        assert a == F(27, 32)
        start = c/(1-a)
        states = []
        x = start
        valid = True
        for bit in word:
            states.append(x)
            valid &= (x.numerator % 2 == int(bit)) and x.denominator % 2 == 1
            x = x/2 if bit == '0' else 3*x+1
        assert x == start
        words += 1
        if valid:
            genuine += 1
            ratios.append(max(states)/min(states))
    assert words == 56 and genuine == 16 and min(ratios) == F(116, 23)
    qs = list(range(10000)) + [2**p-1 for p in (90, 180, 512, 1024)]
    for q in qs:
        values = trajectory(32*q+11, 8)
        assert values == [32*q+11, 96*q+34, 48*q+17, 144*q+52,
                          72*q+26, 36*q+13, 108*q+40, 54*q+20, 27*q+10]
        assert values[-1] < values[0]
        assert 32*values[-1] == 27*values[0]+23
    # Actual integer dynamics and a changed/even denominator must not be conflated.
    assert numerator_step(5, 23) == 74 and trajectory(23, 1)[1] == 70
    assert numerator_step(10, 46) != 74*2
    for n in range(10000):
        assert numerator_step(1, n) == trajectory(n, 1)[1]
    print(f'10000 rational states; {len(scales)} odd scales; {words} exact affine words '
          f'({genuine} parity-valid); {len(qs)} integer traces; bridge and denominator controls passed')


if __name__ == '__main__':
    main()
