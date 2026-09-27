#!/usr/bin/env python3
"""Exploratory biased Syracuse densities, not proof certificates.

Use --alpha 1 for Tao's geometric law. For general alpha > 0 the
valuation distribution is P(v)=(1-q)*q**(v-1), q=2**(-alpha).
See Devices/MultiscaleSyracuse.md for the operator identities and gaps.

The cutoff law is conditioned on v <= cutoff at each step. Its total
variation distance from the full n-step law is at most n*q**cutoff.
This bounds truncation only: float64 rounding is NOT certified here.
"""

import argparse
import math

import numpy as np


def rows(levels, alpha, cutoff):
    q = 2.0 ** (-alpha)
    scale = 3.0 ** (alpha - 1.0) / (2.0 ** alpha - 1.0)
    first_max = 3.0 / (1.0 + q)
    prev = np.ones(1)
    cumulative = np.zeros(1)
    previous_minimum = None
    for n in range(1, levels + 1):
        modulus = 3 ** n
        y = np.arange(modulus // 3, dtype=np.int64)
        base = 3 * y + 1
        mu = np.zeros(modulus)
        inverse = pow(2, -1, modulus)
        factor = 1
        probability = (1.0 - q) / (1.0 - q ** cutoff)
        for _ in range(cutoff):
            factor = factor * inverse % modulus
            mu[base * factor % modulus] += probability * prev
            probability *= q
        density = modulus * mu
        fertile = np.arange(modulus) % 3 != 0
        previous_sum = np.tile(cumulative, 3)
        cumulative = previous_sum + density
        minimum = float(density[fertile].min())
        record = {
            'level': n,
            'minimum_density': minimum,
            'scaled_minimum': n * minimum,
            'minimum_cumulative': float(cumulative[fertile].min()),
            'minimizer': int(np.flatnonzero(fertile)[density[fertile].argmin()]),
            'mass_error': float(abs(mu.sum() - 1.0)),
            'truncation_density_error_bound': modulus * n * q ** cutoff,
        }
        if n > 1:
            record['reciprocal_increment'] = 1 / minimum - 1 / previous_minimum
            record['minimum_class7'] = float(density[7::9].min())
            residues = np.arange(modulus) % 3
            first = np.where(residues == 1, 3 * q / (1 + q), first_max)
            ratio = scale * (1 + (density[fertile] - first[fertile]) /
                             previous_sum[fertile])
            record['sum_vector_ratio'] = float(ratio.min())
            record['block_bound'] = scale * (minimum / first_max) ** (1 / (n - 1))
        yield record
        prev = mu
        previous_minimum = minimum


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--levels', type=int, default=12)
    parser.add_argument('--alpha', type=float, default=1.0)
    parser.add_argument('--cutoff', type=int, default=64)
    args = parser.parse_args()
    if not 1 <= args.levels <= 16:
        parser.error('levels must be in 1..16 (arrays grow as 3**levels)')
    if not math.isfinite(args.alpha) or args.alpha <= 0 or args.cutoff <= 0:
        parser.error('alpha must be finite and positive; cutoff must be positive')
    if not 0 < 2.0 ** (-args.alpha) < 1:
        parser.error('alpha is outside the representable geometric-law range')
    print('FLOATING-POINT EXPLORATION; no certified spectral or asymptotic bound')
    print(' n    min f_n      n*min     min sum    sum ratio  block bound   delta 1/min  trunc error')
    for row in rows(args.levels, args.alpha, args.cutoff):
        print(f"{row['level']:2d} {row['minimum_density']:11.8f} "
              f"{row['scaled_minimum']:10.7f} {row['minimum_cumulative']:10.7f} "
              f"{row.get('sum_vector_ratio', float('nan')):10.7f} "
              f"{row.get('block_bound', float('nan')):11.7f} "
              f"{row.get('reciprocal_increment', float('nan')):12.7f} "
              f"{row['truncation_density_error_bound']:11.2e}")


if __name__ == '__main__':
    main()
