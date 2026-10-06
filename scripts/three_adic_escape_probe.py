#!/usr/bin/env python3
"""Independent integer-orbit regression for ThreeAdicEscape's exact laws.

This executable uses only Python's standard library. Finite checks supplement
Lean proofs; they do not constitute a proof of universal Collatz descent.
"""
import argparse
import json
from pathlib import Path


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def orbit(n: int, k: int) -> int:
    for _ in range(k):
        n = step(n)
    return n


def probe(limit: int, depth: int) -> dict:
    assert limit > 0 and depth >= 0
    counts = [0] * (depth + 1)
    residues = [[0, 0, 0] for _ in range(depth + 1)]
    checks = 0
    for n in range(limit):
        current = n
        escaped = False
        for k in range(depth + 1):
            survives = current % 3 == 0
            expected = n % (3 * (1 << k)) == 0
            assert survives == expected, (n, k, current)
            assert not (escaped and survives), (n, k, current)
            escaped = escaped or not survives
            counts[k] += survives
            residues[k][current % 3] += 1
            current = step(current)
            checks += 1
    for k, count in enumerate(counts):
        d = 3 * (1 << k)
        # The interval contains zero; this exact formula uses ceiling division.
        assert count == (limit + d - 1) // d, (k, count, d)
        assert limit // d <= count <= limit // d + 1
    boundary_checks = 0
    for k in range(depth + 1):
        d = 3 * (1 << k)
        # Include integers well beyond any finite exhaustive input range.
        for q in (1, 2, 3, 17, 10**30 + 1):
            for offset in (-1, 0, 1):
                n = d * q + offset
                actual = orbit(n, k) % 3 == 0
                assert actual == (offset == 0), (k, q, offset)
                boundary_checks += 1
        assert orbit(d, k) == 3
    for n in range(1, min(limit, 1000)):
        assert orbit(n, n) % 3 != 0, n
    return {
        'input_range': [0, limit],
        'range_end_exclusive': True,
        'depth_inclusive': depth,
        'orbit_divisibility_checks': checks,
        'large_integer_boundary_checks': boundary_checks,
        'residue_counts': residues,
        'survivor_counts': counts,
        'status': 'passed',
        'claim_scope': 'finite regression only; universal laws supplied by Lean',
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=100000)
    parser.add_argument('--depth', type=int, default=20)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = probe(args.limit, args.depth)
    serialized = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(serialized)
    print(serialized, end='')


if __name__ == '__main__':
    main()
