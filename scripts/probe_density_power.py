#!/usr/bin/env python3
"""Check the power-bound quantifier example for the halving comparison map."""
import json


def terminal(n):
    while n not in (0, 1, 3):
        n //= 2
    return n


def main():
    limit = 10000
    minima = [terminal(n) for n in range(limit)]
    records = []
    for q in range(1, 9):
        cutoff = 3**q + 1
        flags = [m**q < n for n, m in enumerate(minima)]
        assert all(flags[n] for n in range(cutoff, limit))
        records.append({
            "reciprocal_denominator": q,
            "cofinite_cutoff": cutoff,
            "successful_starts_below_10000": sum(flags),
        })
    for n in range(2, limit):
        # q=n is the witness used in the converse of the pointwise theorem.
        assert (minima[n]**n < n) == (minima[n] == 1)
    failures = sum(n > 0 and m != 1 for n, m in enumerate(minima))
    assert limit <= 8 * failures
    print(json.dumps({
        "comparison_map_not_collatz": True,
        "limit_exclusive": limit,
        "power_thresholds": records,
        "pointwise_equivalence_checks": limit - 2,
        "positive_nonconvergent_starts": failures,
        "all_checks_passed": True,
    }, indent=2))


if __name__ == "__main__":
    main()
