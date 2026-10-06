#!/usr/bin/env python3
"""Independent complete-residue checks of homogeneous parity moments."""
import json
from math import comb
from fractions import Fraction


def odd_count(n, length):
    result = 0
    for _ in range(length):
        if n % 2:
            result += 1
            n = (3 * n + 1) // 2
        else:
            n //= 2
    return result


def main():
    moment_checks = 0
    tail_checks = 0
    residue_checks = 0
    weights = [(0, 0), (1, 0), (1, 1), (2, 1), (11, 10), (63, 62)]
    for k in range(13):
        histogram = [0] * (k + 1)
        for r in range(2**k):
            histogram[odd_count(r, k)] += 1
            residue_checks += 1
        assert histogram == [comb(k, a) for a in range(k + 1)]
        for A, B in weights:
            moment = sum(count * A**a * B**(k-a) for a, count in enumerate(histogram))
            assert moment == (A + B)**k
            moment_checks += 1
            for h in range(k + 2):
                tail = sum(histogram[h:])
                assert A**h * B**max(0, k-h) * tail <= moment
                tail_checks += 1
    moment_numerator = 125**125
    moment_denominator = 2**125 * 63**63 * 62**62
    multiplier_numerator = 3**315
    multiplier_denominator = 2**500
    assert moment_numerator < moment_denominator
    assert multiplier_numerator < multiplier_denominator
    ratio = Fraction(moment_numerator, moment_denominator)
    print(json.dumps({
        "complete_residue_checks": residue_checks,
        "moment_identities_checked": moment_checks,
        "tail_bounds_checked": tail_checks,
        "all_checks_passed": True,
        "four_fifths_parameters": {
            "block_length": 125,
            "odd_threshold": 63,
            "odd_weight": 63,
            "even_weight": 62,
            "normalized_tail_bound_ratio_approx": float(ratio),
            "fifth_power_multiplier_ratio_approx": float(Fraction(multiplier_numerator, multiplier_denominator)),
            "both_gaps_verified_with_exact_integers": True,
        },
        "full_four_fifths_density_theorem_proved_by_this_probe": False,
    }, indent=2))


if __name__ == "__main__":
    main()
