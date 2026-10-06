#!/usr/bin/env python3
"""Exact-integer tests for the general rational-exponent certificate.

Small certificates are searched for the numerical tests. The Lean existence
proof instead uses a coarse closed-form construction valid at every exponent.
"""
import json


def check_certificate(p, q, t):
    K, h, A, B = 2 * (t + 2), t + 3, t + 3, t + 1
    assert K > 0 and h <= K and B <= A and A + B > 0
    assert (A + B)**K < 2**K * A**h * B**(K-h)
    assert 3**(q*h) < 2**(p*K)
    return K


def find_t(p, q):
    left, right = 3**(3*q), 2**(4*p)
    odd_factor, even_factor = 3**q, 2**(2*p)
    for t in range(10000):
        if left < right:
            return t
        left *= odd_factor
        right *= even_factor
    raise AssertionError((p, q, "Search bound exhausted"))


def main():
    balanced = 0
    for t in range(201):
        a = (t + 3) * (t + 1)
        assert (a + 1)**(t + 1) <= a**(t + 1) + (t + 1)*(a + 1)**t
        assert (t + 2)**(2*(t + 2)) < (t + 3)**(t + 3)*(t + 1)**(t + 1)
        balanced += 1
    certificates = []
    excluded = 0
    for q in range(1, 41):
        for p in range(1, 41):
            if 3**q < 4**p:
                t = find_t(p, q)
                certificates.append((p, q, t, check_certificate(p, q, t)))
            else:
                excluded += 1
    explicit = 0
    for q in range(1, 5):
        for p in range(1, 9):
            if 3**q < 4**p:
                t = (3**q)**2
                check_certificate(p, q, t)
                explicit += 1
    scales = 0
    for K in (1, 2, 3, 7, 125, 2592):
        for D in range(1, 5):
            for S in range(5):
                for delta in (0, 1, 100, 2**(K+1)):
                    N = D * 2**(K*S) + delta
                    v = N // D
                    s = (v.bit_length()-1)//K
                    assert S <= s
                    assert D*2**(K*s) <= N < D*2**K*2**(K*s)
                    scales += 1
    sample = [(p, q, t, K) for p, q, t, K in certificates if (p, q) in ((4, 5), (23, 29), (1, 1))]
    print(json.dumps({
        "all_checks_passed": True,
        "balanced_gap_checks": balanced,
        "admissible_exponent_certificates_checked": len(certificates),
        "pairs_excluded_by_strict_threshold": excluded,
        "closed_form_construction_checks": explicit,
        "general_scale_selections_checked": scales,
        "largest_searched_block": max(K for _, _, _, K in certificates),
        "sample_certificates": [dict(numerator=p, denominator=q, t=t, block=K) for p, q, t, K in sample],
        "proves_universal_convergence": False,
    }, indent=2))


if __name__ == "__main__":
    main()
