#!/usr/bin/env python3
"""Check first-descent semantics, size bounds, and selected-time count covers."""
import json
from functools import lru_cache


def step(n):
    return n//2 if n%2 == 0 else (3*n+1)//2


def orbit(n, k):
    for _ in range(k):
        n = step(n)
    return n


@lru_cache(None)
def first_descent(n):
    if n <= 1:
        return 0, n
    m = n
    for k in range(1, 10000):
        m = step(m)
        if m < n:
            return k, m
    raise AssertionError((n, "Probe did not resolve first descent"))


def main():
    for n in range(10000):
        time, target = first_descent(n)
        assert target == orbit(n, time)
        assert all(n <= orbit(n, j) for j in range(time))
        assert (target < n) == (n > 1)
        assert n <= 2*target
        if n >= 32:
            assert n**4 <= target**5
    covers = 0
    predicates = [lambda n: n%2 == 0, lambda n: n%7 == 3, lambda n: n>10]
    rules = [lambda n: n%11, lambda n: n.bit_length(), lambda n: first_descent(n)[0]]
    for P in predicates:
        for time in rules:
            for K in (0, 1, 2, 5, 10):
                bad = tail = window_bad = 0
                for N in range(501):
                    if N:
                        n = N-1
                        bad += not P(orbit(n, time(n)))
                        tail += time(n)>K
                        window_bad += not all(P(orbit(n, j)) for j in range(K+1))
                    assert bad <= tail+window_bad
                    covers += 1
    distributions = []
    for N in (1000, 10000):
        records = []
        for H in (0, 1, 2, 4, 8, 16, 32, 64, 128):
            time_tail = sum(first_descent(n)[0]>H for n in range(N))
            no_drop = sum(all(n <= orbit(n, j) for j in range(H+1)) for n in range(N))
            assert time_tail <= no_drop
            records.append({"horizon": H, "time_tail": time_tail, "no_drop_count": no_drop})
        distributions.append({"cutoff_exclusive": N, "records": records})
    print(json.dumps({
        "all_checks_passed": True,
        "first_descent_inputs_checked": 10000,
        "selected_time_count_covers_checked": covers,
        "maximum_first_descent_time": max(first_descent(n)[0] for n in range(10000)),
        "first_time_tail_distributions": distributions,
        "proves_universal_convergence": False,
    }, indent=2))


if __name__ == "__main__":
    main()
