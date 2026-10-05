#!/usr/bin/env python3
"""Independent exact-rational checks of the Beatty phase certificate.

Exploration and reproducibility only: Lean checks the universal inequalities.
"""
import json
from fractions import Fraction as Q


def step(r):
    return (4 if 4 * r <= 3 else 2) * r / 3


def phase_sum(r, length):
    total = Q(0)
    for _ in range(length):
        total += r
        r = step(r)
    return total


def endpoints(length):
    return sorted({Q(1)} | {
        Q(3**i, 2 ** (3**i).bit_length()) for i in range(1, length)
    })


def maximum(length):
    return max((phase_sum(r, length), r) for r in endpoints(length))


def certificate(length):
    left = Q(1, 2)
    rows = []
    for right in endpoints(length):
        multiplier, slope, branches = 1, Q(0), []
        for j in range(length):
            slope += Q(multiplier, 3**j)
            if j + 1 == length:
                break
            # Prove the branch for every point in (left, right], not samples.
            if 4 * multiplier * right <= 3 ** (j + 1):
                multiplier *= 4
                branches.append("low")
            else:
                assert 4 * multiplier * left >= 3 ** (j + 1)
                multiplier *= 2
                branches.append("high")
        assert phase_sum(right, length) == slope * right
        rows.append({"left_open": str(left), "right_closed": str(right),
                     "sum_slope": str(slope),
                     "certified_branches": branches,
                     "maximum": str(slope * right)})
        left = right
    return rows


def main():
    best, witness = maximum(12)
    assert best == Q(2349463, 262144)
    assert witness == Q(177147, 262144)
    assert best < 9
    short = []
    for length in range(1, 12):
        value, phase = maximum(length)
        assert value > Q(3 * length, 4)
        assert value - Q(3 * length, 4) <= Q(11, 36)
        short.append({"length": length, "maximum": str(value),
                      "phase": str(phase),
                      "excess_above_three_quarters": str(value - Q(3 * length, 4))})
    b, p3, p2 = 0, 1, 1
    equality_indices = []
    for a in range(1001):
        assert 108 * b <= (27 * a + 11) * p3
        if 108 * b == (27 * a + 11) * p3:
            equality_indices.append(a)
        b, p3, p2 = (3 * b + p2, 3 * p3,
                       (4 if 4 * p2 <= 3 * p3 else 2) * p2)
    assert equality_indices == [3]
    print(json.dumps({
        "arithmetic": "exact rational and integer",
        "twelve_step_supremum": str(best),
        "maximizing_phase": str(witness),
        "margin_below_nine": str(9 - best),
        "twelve_phase_intervals": certificate(12),
        "shorter_block_obstructions": short,
        "initial_remainder_excess": [str(phase_sum(Q(1), k) - Q(3*k, 4))
                                     for k in range(12)],
        "bcap_check_through": 1000,
        "equality_indices_in_check": equality_indices,
        "scope": "Independent checks; universal proof is in Lean."
    }, indent=2))


if __name__ == "__main__":
    main()
