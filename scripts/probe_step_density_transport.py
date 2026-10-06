#!/usr/bin/env python3
"""Independent finite checks of step-count transport and stopping windows."""
import json
from functools import lru_cache
from math import isqrt


def step(n):
    return n // 2 if n % 2 == 0 else (3*n+1)//2


@lru_cache(None)
def has_drop(n):
    if n <= 1:
        return False
    m = n
    for _ in range(10000):
        m = step(m)
        if m < n:
            return True
    raise AssertionError((n, "Probe did not decide finite stopping"))


def main():
    predicates = [
        lambda n: n % 2 == 0,
        lambda n: n % 7 in (1, 3, 5),
        lambda n: n > 0 and n & (n-1) == 0,
        lambda n: isqrt(n)**2 == n,
        lambda n: n.bit_count() % 2 == 0,
        lambda n: 17 <= n < 83,
    ]
    branch_checks = transport_checks = stride_checks = 0
    for P in predicates:
        count = [0]
        pulled = [0]
        for n in range(3001):
            count.append(count[-1]+P(n))
            pulled.append(pulled[-1]+P(step(n)))
        odd_sum = 0
        for N in range(1001):
            if N:
                odd_sum += P(3*(N-1)+2)
            assert pulled[2*N] == count[N]+odd_sum
            assert pulled[N] <= 2*count[3*N]
            branch_checks += 1
            transport_checks += 1
        for d in range(1, 8):
            for r in range(d):
                subtotal = 0
                for N in range(101):
                    if N:
                        subtotal += P(d*(N-1)+r)
                    assert subtotal <= count[d*N]
                    stride_checks += 1
    iterate_checks = 0
    for P in predicates:
        target = [0]
        for n in range(3**5*50):
            target.append(target[-1]+P(n))
        for k in range(6):
            pulled = 0
            for N in range(51):
                if N:
                    value = N-1
                    for _ in range(k):
                        value = step(value)
                    pulled += P(value)
                assert pulled <= 2**k * target[3**k*N]
                iterate_checks += 1
    first_one = [0, 0]
    for n in range(2, 10000):
        m = n
        for k in range(10000):
            if m == 1:
                assert not has_drop(m)
                first_one.append(k)
                break
            assert has_drop(m)
            m = step(m)
        else:
            raise AssertionError((n, "Probe did not reach the terminal orbit"))
    windows = []
    for N in (1000, 10000):
        windows.append({
            "cutoff_exclusive": N,
            "counts_by_window": {str(K): sum(t > K for t in first_one[:N])
                                 for K in (0, 1, 2, 5, 10, 20, 50, 100, 200)},
        })
    print(json.dumps({
        "all_checks_passed": True,
        "exact_branch_counts_checked": branch_checks,
        "preimage_count_bounds_checked": transport_checks,
        "stride_count_bounds_checked": stride_checks,
        "iterate_count_bounds_checked": iterate_checks,
        "positive_starts_with_verified_terminal_never_dropper": len(first_one)-1,
        "maximum_first_one_time": max(first_one),
        "stopping_window_counts": windows,
        "proves_universal_convergence": False,
    }, indent=2))


if __name__ == "__main__":
    main()
