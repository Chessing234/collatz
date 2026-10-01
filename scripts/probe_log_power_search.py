#!/usr/bin/env python3
"""Check rolling scan semantics and measure finite logarithmic-window success."""
import json


def step(n):
    return n//2 if n%2 == 0 else (3*n+1)//2


def orbit(n, k):
    for _ in range(k):
        n = step(n)
    return n


def scan(p, q, target, fuel, current):
    for k in range(fuel+1):
        if current**q < target**p:
            return k
        if k < fuel:
            current = step(current)
    return None


def main():
    exact_checks = 0
    for p, q in ((0, 0), (0, 1), (1, 1), (1, 2), (3, 4), (4, 5), (23, 29)):
        for target in range(21):
            for current in range(21):
                for fuel in range(8):
                    result = scan(p, q, target, fuel, current)
                    expected = [k for k in range(fuel+1) if orbit(current, k)**q < target**p]
                    assert result == (expected[0] if expected else None)
                    exact_checks += 1
    results = []
    for p, q in ((3, 4), (4, 5), (23, 29), (1, 1)):
        successes = 0
        max_time = 0
        snapshots = []
        for n in range(100000):
            fuel = max(0, n.bit_length()-1)
            result = scan(p, q, n, fuel, n)
            if result is not None:
                successes += 1
                max_time = max(max_time, result)
                assert result <= fuel
                if p < q:
                    assert n**(q-p) < 2**(q*result)
            if n+1 in (1000, 10000, 100000):
                snapshots.append({"cutoff_exclusive": n+1, "successes": successes})
        results.append({"numerator": p, "denominator": q,
                        "in_recorded_korec_range": 3**q < 4**p,
                        "maximum_observed_success_time": max_time,
                        "counts": snapshots})
    failed_but_later = None
    for n in range(2, 10000):
        fuel = n.bit_length()-1
        if scan(4, 5, n, fuel, n) is None:
            later = scan(4, 5, n, 1000, n)
            if later is not None:
                failed_but_later = {"start": n, "log_window": fuel, "later_hit": later}
                break
    assert failed_but_later is not None
    print(json.dumps({"all_checks_passed": True,
                      "scan_semantics_checks": exact_checks,
                      "finite_success_counts": results,
                      "failed_window_with_later_success": failed_but_later,
                      "proves_universal_success": False}, indent=2))


if __name__ == "__main__":
    main()
