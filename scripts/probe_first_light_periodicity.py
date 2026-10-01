#!/usr/bin/env python3
"""Independent finite checks of parity-class survival and actual first descent.

This is regression evidence, not a substitute for the Lean proofs. The dynamic
program counts binary words satisfying every coefficient-prefix inequality;
exhaustive residues check the connection with actual accelerated trajectories.
"""
import argparse
import json


def profile(n, horizon):
    x, odds = n, 0
    first_light = first_drop = None
    for k in range(1, horizon + 1):
        odd = x % 2
        odds += odd
        x = (3*x + 1)//2 if odd else x//2
        if first_light is None and 3**odds < 2**k:
            first_light = k
        if first_drop is None and x < n:
            first_drop = k
    return first_light, first_drop


def word_count(horizon):
    counts = {0: 1}
    for k in range(1, horizon + 1):
        nxt = {}
        for a, count in counts.items():
            for b in (a, a+1):
                if 2**k <= 3**b:
                    nxt[b] = nxt.get(b, 0) + count
        counts = nxt
    return sum(counts.values())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-horizon', type=int, default=16)
    args = parser.parse_args()
    if not 0 <= args.max_horizon <= 20:
        parser.error('max-horizon must be between 0 and 20')
    rows = []
    for h in range(args.max_horizon + 1):
        period = 2**h
        bits = []
        for r in range(period):
            # Both representatives are >1, including residue classes 0 and 1.
            small = profile(r + 2*period, h)
            large = profile(r + 3*period, h)
            assert small == large, (h, r, small, large)
            assert small[0] == small[1], (h, r, small)
            bits.append(small[0] is None)
        count = sum(bits)
        assert count == word_count(h), (h, count, word_count(h))
        shifted = [bits[(n+2) % period] for n in range(period)]
        for n in (0, 1, period-1, period, period+1, 3*period+7):
            observed = sum(shifted[j % period] for j in range(n))
            expected = (n//period)*count + sum(shifted[:n % period])
            assert observed == expected, (h, n, observed, expected)
        rows.append({'horizon': h, 'period': period, 'surviving_classes': count})
    print(json.dumps({'status': 'passed', 'rows': rows}, indent=2))


if __name__ == '__main__':
    main()
