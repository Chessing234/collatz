#!/usr/bin/env python3
"""Finite experiments for rational orbit bounds, using only integer powers."""
import argparse
import json


def first_below(n, p, q, horizon):
    x, bound = n, n**p
    for k in range(horizon + 1):
        if x**q < bound:
            return k
        x = (3*x+1)//2 if x % 2 else x//2
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--cutoff', type=int, default=10000)
    args = parser.parse_args()
    if args.cutoff < 3:
        parser.error('cutoff must exceed 2')
    assert first_below(0, 4, 5, 256) is None
    assert first_below(1, 4, 5, 256) is None
    assert first_below(2, 4, 5, 256) == 1
    rows = []
    for p, q in ((4, 5), (3, 4)):
        witnesses = [first_below(n, p, q, 256) for n in range(args.cutoff)]
        rows.append({
            'numerator': p, 'denominator': q,
            'inside_published_exponent_range': 3**q < 4**p,
            'counts_below_cutoff': {str(h): sum(k is not None and k <= h for k in witnesses)
                                    for h in (0, 4, 16, 64, 256)},
            'maximum_found_index': max(k for k in witnesses if k is not None),
        })
    print(json.dumps({'cutoff': args.cutoff, 'rows': rows,
                     'scope': 'Finite evidence only; not a density theorem.'}, indent=2))


if __name__ == '__main__':
    main()
