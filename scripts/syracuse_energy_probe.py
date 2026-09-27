#!/usr/bin/env python3
"""Finite energy exploration, not an all-depth bound or a Lean certificate.

The first five energies are cross-checked against full-period Fraction laws.
Higher levels use float64 and an 80-valuation cutoff. Rounding is not certified.
The cutoff loses at most n*2^-80 total probability at level n.
"""
import argparse
import json

import numpy as np

from check_syracuse_cycle_scan import exact_laws


def probe(levels):
    exact = [len(law) * sum(x*x for x in law) for law in exact_laws(5)]
    previous = np.ones(1)
    prior_energy = 1.0
    for n in range(1, levels + 1):
        modulus = 3**n
        base = 3*np.arange(modulus//3, dtype=np.int64)+1
        current = np.zeros(modulus)
        inverse = pow(2, -1, modulus)
        factor, probability = 1, 0.5
        for _ in range(80):
            factor = factor*inverse % modulus
            current[base*factor % modulus] += probability*previous
            probability *= 0.5
        density = modulus*current
        energy = float(np.dot(density, current))
        recurrence_gain = float(2*(modulus//3)*np.dot(current[1::3], previous))
        assert abs(energy-prior_energy-recurrence_gain) < 1e-10
        row = {
            "level": n, "status": "floating_point_exploration",
            "energy": energy, "gain": recurrence_gain,
            "fractional_moments": {
                str(p): float(np.mean(density**p)) for p in (1.25, 1.5, 1.75, 1.9)
            },
            "cutoff_probability_loss_bound": n*2.0**-80,
        }
        if n <= len(exact):
            assert abs(energy-float(exact[n-1])) < 1e-11
            row["exact_energy_fraction"] = str(exact[n-1])
        yield row
        previous, prior_energy = current, energy


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--levels", type=int, default=14)
    args = parser.parse_args()
    if not 1 <= args.levels <= 16:
        parser.error("levels must be in 1..16")
    for row in probe(args.levels):
        print(json.dumps(row), flush=True)


if __name__ == "__main__":
    main()
