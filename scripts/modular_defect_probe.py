"""Exact exploration of single-defect periodic Collatz labels.

Each input class modulo 2m is a separate edge; parallel edges are retained.
Bridge detection characterizes cuts with exactly one defect. This experiment
is not a proof for unbounded moduli.
"""

import argparse
import json
import sys


def bridges(m):
    graph = [[] for _ in range(m)]
    for n in range(2 * m):
        target = (n // 2 if n % 2 == 0 else (3 * n + 1) // 2) % m
        source = n % m
        graph[source].append((target, n))
        graph[target].append((source, n))
    entered = [-1] * m
    low = [0] * m
    clock = 0
    result = []

    def visit(vertex, parent_edge):
        nonlocal clock
        entered[vertex] = low[vertex] = clock
        clock += 1
        for target, edge in graph[vertex]:
            if edge == parent_edge:
                continue
            if entered[target] == -1:
                visit(target, edge)
                low[vertex] = min(low[vertex], low[target])
                if low[target] > entered[vertex]:
                    result.append(edge)
            else:
                low[vertex] = min(low[vertex], entered[target])

    visit(0, -1)
    assert all(time >= 0 for time in entered), (m, "disconnected")
    return sorted(result)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-modulus", type=int, default=2000)
    args = parser.parse_args()
    sys.setrecursionlimit(max(10000, 3 * args.max_modulus))
    failures = []
    for m in range(2, args.max_modulus + 1):
        actual = bridges(m)
        expected = [m] if m % 3 == 0 else []
        if actual != expected:
            failures.append({"modulus": m, "bridges": actual, "expected": expected})
    print(json.dumps({"max_modulus": args.max_modulus,
                      "hypothesis": "only bridge is input m when 3 divides m",
                      "failures": failures}, indent=2))


if __name__ == "__main__":
    main()
