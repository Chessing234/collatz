#!/usr/bin/env python3
"""Check the size-time barrier on actual orbits and first power-hit times."""
import json


def step(n):
    return n//2 if n%2 == 0 else (3*n+1)//2


def first_hit(n, p, q):
    m = n
    for k in range(1000):
        if m**q < n**p:
            assert n**(q-p) < 2**(k*q)
            return k
        m = step(m)
    raise AssertionError((n, p, q, "Probe did not find a power hit"))


def main():
    hits = 0
    lower_checks = 0
    exponent_pairs = [(0, 1), (1, 2), (3, 4), (4, 5), (23, 29)]
    for n in range(3000):
        m = n
        for k in range(51):
            assert n <= 2**k * m
            lower_checks += 1
            for p, q in exponent_pairs:
                if m**q < n**p:
                    assert n**(q-p) < 2**(k*q)
                    assert n < 2**(k*q)
                    hits += 1
            m = step(m)
    window_checks = 0
    for p, q in ((1, 2), (3, 4), (4, 5)):
        for K in range(5):
            B = 2**(K*q)
            for n in range(B, B+100):
                m = n
                for _ in range(K+1):
                    assert not m**q < n**p
                    m = step(m)
                    window_checks += 1
    records = []
    for p, q in ((1, 2), (3, 4), (4, 5), (23, 29)):
        times = [first_hit(n, p, q) for n in range(2, 10000)]
        records.append({
            "numerator": p,
            "denominator": q,
            "inputs_checked": len(times),
            "maximum_first_hit_time": max(times),
            "first_hit_tail_counts": {str(K): sum(t > K for t in times) for K in (1, 2, 4, 8, 16, 32, 64)},
        })
    print(json.dumps({
        "all_checks_passed": True,
        "halving_lower_bounds_checked": lower_checks,
        "successful_power_hits_checked": hits,
        "forbidden_window_checks": window_checks,
        "first_hit_samples": records,
        "first_hit_samples_do_not_evaluate_classical_choice": True,
        "proves_universal_convergence": False,
    }, indent=2))


if __name__ == "__main__":
    main()
