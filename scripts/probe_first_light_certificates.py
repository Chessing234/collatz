#!/usr/bin/env python3
"""Compute and test first-crossing certificates with exact integer arithmetic.

The probe supplies evidence, not a proof. Lean must separately verify both
finite certificates and apply the generic soundness theorem.
"""
import argparse
import json


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--horizon', type=int, default=256)
    args = parser.parse_args()
    if args.horizon < 1:
        parser.error('horizon must be positive')
    horizon = args.horizon
    worst = (0, 0, 0)
    # The gap ratio is increasing in a; find the largest light odd count.
    a = 0
    for k in range(1, horizon + 1):
        while 3 ** (a + 1) < 2**k:
            a += 1
        bound = a * 3**a // (3 * (2**k - 3**a))
        if bound > worst[0]:
            worst = (bound, k, a)
    threshold = worst[0] + 1
    # Verify every table entry independently of the extremal-count reduction.
    for k in range(horizon + 1):
        two = 2**k
        three = 1
        for odd in range(k + 1):
            if three < two:
                assert odd * three < 3 * (two - three) * threshold
            three *= 3
    maximum = (0, 0)
    for n in range(2, threshold):
        x, odd = n, 0
        for k in range(1, horizon + 1):
            odd += x % 2
            x = (3*x+1)//2 if x % 2 else x//2
            if 3**odd < 2**k:
                assert x < n, ('descent failure', n, k, x)
                if k > maximum[0]:
                    maximum = (k, n)
                break
        else:
            raise AssertionError(('no first crossing within horizon', n))
    print(json.dumps({'horizon': horizon, 'exception_threshold': threshold,
                     'small_starts_checked': max(0, threshold-2),
                     'worst_gap_pair': {'k': worst[1], 'odd_count': worst[2]},
                     'maximum_first_crossing': {'k': maximum[0], 'start': maximum[1]},
                     'failures': 0, 'universal_descent_proved': False}, indent=2))


if __name__ == '__main__':
    main()
