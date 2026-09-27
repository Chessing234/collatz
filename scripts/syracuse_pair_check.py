#!/usr/bin/env python3
"""Exact integer interval check of a proposed Syracuse pair lower bound.

This is not a Lean certificate. No floating-point operation decides the
result. NumPy uint64 arithmetic computes lower bounds B_n/S for every atom
of the actual Syracuse law modulo 3**n, with S=2**precision.

At each valuation v<=cutoff, add floor(B_prev/2**v) at its image. The image
map is injective for fixed v, so NumPy's indexed addition has no repeated
indices within an addition. Each partial sum is <= S (a subprobability
mass), and all modular products fit int64 within the parameter limits.

If each previous atom error is <= E/S, the next error is at most
(E + cutoff + 2**(precision-cutoff))/S: rounding costs at most cutoff/S,
the omitted tail at most 2**(-cutoff), and previous errors at most E/S.
Thus E_n=n*(cutoff+2**(precision-cutoff)) is a uniform error bound.

Let m be the minimum normalized density and J=f(a)+f(4a+1)/4. We test
J < 21*m/(4*(1+3*m)) using an upper bound on J and lower bound on m.
That rational function is increasing, so a strict comparison refutes the
proposed lower bound. It does NOT refute the logistic recurrence for m.
"""

import argparse
import json

import numpy as np


def check(levels=14, precision=60, cutoff=60, residue=1292371):
    if not (1 <= levels <= 15 and 1 <= cutoff <= precision <= 62):
        raise ValueError('require levels in 1..15 and 1 <= cutoff <= precision <= 62')
    scale = 1 << precision
    previous = np.array([scale], dtype=np.uint64)
    for n in range(1, levels + 1):
        modulus = 3 ** n
        base = 3 * np.arange(modulus // 3, dtype=np.int64) + 1
        lower = np.zeros(modulus, dtype=np.uint64)
        inverse = pow(2, -1, modulus)
        factor = 1
        for v in range(1, cutoff + 1):
            factor = factor * inverse % modulus
            lower[(base * factor) % modulus] += previous >> v
        previous = lower
    a = residue % modulus
    if a % 3 != 1:
        raise ValueError('the first residue must be 1 modulo 3')
    b = (4 * a + 1) % modulus
    minimum = min(int(lower[1::3].min()), int(lower[2::3].min()))
    error = levels * (cutoff + (1 << (precision - cutoff)))
    pair_upper = 4 * int(lower[a]) + int(lower[b]) + 5 * error
    left = pair_upper * (scale + 3 * modulus * minimum)
    right = 21 * minimum * scale
    return {
        'status': 'exact integer interval calculation; not Lean-verified',
        'levels': levels, 'precision': precision, 'cutoff': cutoff,
        'modulus': modulus, 'scale': scale, 'a': a, 'b': b,
        'minimum_atom_lower_numerator': minimum,
        'a_atom_lower_numerator': int(lower[a]),
        'b_atom_lower_numerator': int(lower[b]),
        'uniform_atom_error_numerator': error,
        'pair_upper_numerator_before_normalization': pair_upper,
        'comparison_left': left, 'comparison_right': right,
        'strict_margin': right - left,
        'proposed_pair_bound_refuted': left < right,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--levels', type=int, default=14)
    parser.add_argument('--precision', type=int, default=60)
    parser.add_argument('--cutoff', type=int, default=60)
    parser.add_argument('--residue', type=int, default=1292371)
    args = parser.parse_args()
    result = check(args.levels, args.precision, args.cutoff, args.residue)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
