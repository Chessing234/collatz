#!/usr/bin/env python3
"""Comparison-map regression: finite stopping is distinct from reaching 1."""
import json


def step(n):
    return n if n in (0, 1, 3) else n//2


def main():
    stop_count = failure_count = 0
    cutoff = 10000
    for n in range(cutoff):
        x = n
        while x not in (0, 1, 3):
            x = step(x)
        assert n == 0 or x in (1, 3)
        stops = step(n) < n
        fails = n > 0 and x != 1
        stop_count += stops
        failure_count += fails
        N = n+1
        if N >= 4:
            assert stop_count == N-3
            assert N <= 8*failure_count
    print(json.dumps({'comparison_map_not_collatz': True, 'cutoff': cutoff,
                      'finite_stopping_count': stop_count,
                      'positive_nonconvergent_count': failure_count,
                      'assertions': 'passed'}, indent=2))


if __name__ == '__main__':
    main()
