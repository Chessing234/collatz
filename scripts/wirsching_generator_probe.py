#!/usr/bin/env python3
"""Exact finite exploration of Wirsching's fixed-cost generators.

This is an experiment, not a Lean certificate or an asymptotic proof.
The recursion is equation (2.1) of Wirsching's 2003 paper:
  g_(l+1)(k,a) = sum_(0<=j<2*3^l) g_l(k-j,(2^(j+1)*a-1)/3).
For l>=1 the generator is zero outside the 3-adic units; g_0 is the
indicator of k=0 on all integral 3-adic arguments. We compute all unit
residues at each depth and compare their sum to the independent product
of polynomials (1+z+...+z^(2*3^i-1)), 0<=i<l.
"""

import argparse
import json
from collections import Counter
from fractions import Fraction
from math import comb, isqrt

import numpy as np


def probe(depth: int, radius: int) -> dict:
    if depth < 1 or radius < 0:
        raise ValueError('depth must be positive and radius nonnegative')
    max_cost = depth + radius
    # An individual cell counts a subset of weak compositions into depth
    # coordinates. This bound also controls every nonnegative partial sum.
    bound = comb(max_cost + depth - 1, depth - 1)
    if bound * 3**depth > np.iinfo(np.int64).max:
        raise ValueError('requested range exceeds the proven int64 bound')
    if (3**depth)**2 > np.iinfo(np.int64).max:
        raise ValueError('residue multiplication exceeds int64 capacity')

    previous = np.zeros((max_cost + 1, 1), dtype=np.int64)
    previous[0, 0] = 1
    forward = Counter({(0, 0): 1})
    polynomial = [1] + [0] * max_cost
    rows = []
    for level in range(1, depth + 1):
        modulus = 3**level
        old_modulus = modulus // 3
        residues = np.arange(modulus, dtype=np.int64)
        units = residues % 3 != 0
        current = np.zeros((max_cost + 1, modulus), dtype=np.int64)
        max_jump = min(max_cost, 2 * old_modulus - 1)
        for jump in range(max_jump + 1):
            numerator = pow(2, jump + 1, modulus) * residues - 1
            valid = units & (numerator % 3 == 0)
            preimage = (numerator[valid] // 3) % old_modulus
            current[jump:, valid] += previous[:max_cost + 1 - jump, preimage]
        polynomial = [sum(polynomial[k-j] for j in range(min(k, max_jump) + 1))
                      for k in range(max_cost + 1)]
        totals = current.sum(axis=1)
        if list(map(int, totals)) != polynomial:
            raise AssertionError(f'path-count polynomial mismatch at depth {level}')
        # Independently build residues forward using arbitrary-precision
        # Python integers, rather than the vectorized inverse lookup.
        if level <= 5:
            next_forward = Counter()
            for (cost, residue), count in forward.items():
                for jump in range(min(max_cost-cost, max_jump) + 1):
                    child = ((3*residue+1) * pow(pow(2, jump+1, modulus), -1, modulus)) % modulus
                    next_forward[cost+jump, child] += count
            for cost in range(max_cost+1):
                for residue in range(modulus):
                    if int(current[cost, residue]) != next_forward[cost, residue]:
                        raise AssertionError(f'forward/inverse mismatch at {(level, cost, residue)}')
            forward = next_forward
        for cost in range(max(0, level-radius), min(max_cost, level+radius) + 1):
            values = current[cost, units]
            minimum = int(values.min())
            total = int(totals[cost])
            ratio = Fraction(minimum * int(units.sum()), total) if total else None
            least_index = int(np.flatnonzero(units)[int(values.argmin())])
            rows.append(dict(depth=level, cost=cost, unit_residues=int(units.sum()),
                             minimum=minimum, minimum_residue=least_index,
                             zero_residues=int((values == 0).sum()), total=total,
                             minimum_to_mean=str(ratio)))
        previous = current
    return dict(status='finite experiment; not a Lean proof', depth=depth,
                radius=radius, exact_integer_bound=bound,
                all_polynomial_checks_passed=True,
                forward_inverse_checked_through=min(depth, 5), rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=12)
    parser.add_argument('--radius', type=int, default=None)
    args = parser.parse_args()
    radius = isqrt(args.depth) if args.radius is None else args.radius
    print(json.dumps(probe(args.depth, radius), indent=2))
