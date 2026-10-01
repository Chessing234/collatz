#!/usr/bin/env python3
"""Check predecessor counts by enumerating trajectories of the comparison map.

The map is not Collatz. Enumerating complete trajectories independently checks
the cutoff convention and density inequality used by the Lean block argument.
"""
import json


def step(n):
    if n <= 1 or n == 3:
        return n
    return n // 2


def main():
    limit, targets = 10000, 32
    counts = [0] * (targets + 1)
    checked = 0
    basins = {1: 0, 3: 0}
    for cutoff in range(1, limit + 1):
        n = cutoff - 1
        seen = set()
        cur = n
        while cur not in seen:
            seen.add(cur)
            cur = step(cur)
        if n:
            assert cur in basins, (n, cur)
            basins[cur] += 1
        for target in seen:
            if 1 <= target <= targets:
                counts[target] += 1
        for target in range(1, targets + 1):
            base = max(target, 2)
            if cutoff >= base + 1:
                assert cutoff < 2 * (base + 1) * counts[target], (target, cutoff)
                checked += 1
    print(json.dumps({"status": "passed", "cutoff_max": limit,
                      "target_max": targets, "density_checks": checked,
                      "positive_start_basin_counts": basins,
                      "map": "fixed at 1 and 3; otherwise floor(n/2)"}, indent=2))


if __name__ == '__main__':
    main()
