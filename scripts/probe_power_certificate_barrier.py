#!/usr/bin/env python3
"""Exhaust small homogeneous moment certificates and check their boundary."""
import json


def main():
    low_checks = 0
    moment_gaps = 0
    multiplier_checks = 0
    certificates = 0
    exponents = set()
    for A in range(11):
        for B in range(A + 1):
            assert 4 * A * B <= (A + B)**2
            for K in range(13):
                for h in range(K + 1):
                    weight = A**h * B**(K-h)
                    if 2 * h <= K:
                        assert weight**2 <= (A * B)**K
                        assert 2**K * weight <= (A + B)**K
                        low_checks += 1
                    if (A + B)**K < 2**K * weight:
                        assert K < 2 * h
                        moment_gaps += 1
                        for p in range(9):
                            for q in range(9):
                                multiplier_checks += 1
                                if 3**(q*h) < 2**(p*K):
                                    assert 3**q < 4**p
                                    certificates += 1
                                    exponents.add((p, q))
    assert (3, 4) not in exponents
    assert (1, 1) in exponents
    print(json.dumps({
        "all_checks_passed": True,
        "low_threshold_weight_checks": low_checks,
        "strict_moment_gaps_found": moment_gaps,
        "multiplier_conditions_checked": multiplier_checks,
        "valid_certificates_found": certificates,
        "distinct_exponent_pairs_certified": len(exponents),
        "three_quarters_certificate_found": (3, 4) in exponents,
        "invalidates_three_quarters_collatz_density": False,
        "search_limits": {"maximum_odd_weight": 10, "maximum_block": 12, "maximum_numerator_and_denominator": 8},
    }, indent=2))


if __name__ == "__main__":
    main()
