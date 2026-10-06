#!/usr/bin/env python3
"""Independent checks for the core-only 4/5 density proof's interfaces.

The theorem's deliberately coarse eventual cutoffs are not computationally
practical. These tests check its algebraic pieces and actual orbit bounds;
they do not substitute a finite sample for the density theorem.
"""
import json
from random import Random


def orbit(n, k):
    a = 0
    for _ in range(k):
        if n % 2:
            a += 1
            n = (3 * n + 1) // 2
        else:
            n //= 2
    return n, a


def main():
    random = Random(1256362)
    geometric = 0
    for a in range(1, 11):
        for b in range(a + 1, a + 5):
            for q in range(11):
                for delta in range(4):
                    s = q * a + delta
                    assert (a + s) * a**s <= a * b**s
                    assert q * a**s < b**s
                    geometric += 1
    selections = 0
    for D in range(1, 21):
        for S in range(7):
            for delta in (0, 1, 100, 2**126):
                N = D * 2**(125 * S) + delta
                v = N // D
                s = (v.bit_length() - 1) // 125
                M = 2**(125 * s)
                assert S <= s and D * M <= N < D * 2**125 * M
                selections += 1
    count_checks = 0
    for q in range(1, 11):
        for M in range(1, 31):
            for N in range(2 * q * M, 2 * q * M + 8):
                for E in range(M // (4 * q) + 1):
                    F = M + (N // M + 1) * E
                    assert q * F <= N
                    count_checks += 1
    orbit_checks = 0
    scale_certified = 0
    max_bits = 0
    for s in (1, 2, 4, 8, 16, 32, 64):
        k = 125 * s
        M = 2**k
        for L in (1, 2, 10, 100):
            for _ in range(10):
                n = M + random.randrange(max(1, (L - 1) * M))
                m, a = orbit(n, k)
                assert m <= (L + 1) * 3**a
                orbit_checks += 1
                max_bits = max(max_bits, n.bit_length())
                if a <= 63 * s and (L + 1)**5 * 3**(315 * s) < 2**(500 * s):
                    assert m**5 < n**4
                    scale_certified += 1
    finite_targets = 0
    max_steps = 0
    for n in range(2, 10000):
        m = n
        for k in range(1000):
            if m**5 < n**4:
                finite_targets += 1
                max_steps = max(max_steps, k)
                break
            m = m // 2 if m % 2 == 0 else (3 * m + 1) // 2
        else:
            raise AssertionError((n, "No power target found in probe horizon"))
    print(json.dumps({
        "all_checks_passed": True,
        "geometric_inequalities_checked": geometric,
        "scale_selections_checked": selections,
        "prefix_period_estimates_checked": count_checks,
        "actual_orbit_upper_bounds_checked": orbit_checks,
        "power_targets_certified_by_scale_gap": scale_certified,
        "maximum_sample_input_bits": max_bits,
        "starts_2_through_9999_reaching_power_target": finite_targets,
        "maximum_first_power_target_time_in_finite_probe": max_steps,
        "proves_universal_convergence": False,
    }, indent=2))


if __name__ == "__main__":
    main()
