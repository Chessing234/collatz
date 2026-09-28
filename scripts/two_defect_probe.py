"""Independent finite multigraph check; never used as a Lean premise."""
import argparse
import json
import sys


def cuts_of_size_two(m):
    edges = [(n % m, (n // 2 if n % 2 == 0 else (3*n+1)//2) % m)
             for n in range(2*m)]
    adj = [[] for _ in range(m)]
    for j, (a, b) in enumerate(edges):
        adj[a].append((b, j))
        adj[b].append((a, j))
    cuts = set()
    # Delete each edge, then find bridges with edge IDs (parallel edges retained).
    for removed in range(2*m):
        tin, low, timer = [-1]*m, [0]*m, [0]

        def dfs(v, parent_edge):
            tin[v] = low[v] = timer[0]
            timer[0] += 1
            subtree = {v}
            for w, edge_id in adj[v]:
                if edge_id in (removed, parent_edge):
                    continue
                if tin[w] >= 0:
                    low[v] = min(low[v], tin[w])
                else:
                    child = dfs(w, edge_id)
                    subtree |= child
                    low[v] = min(low[v], low[w])
                    if low[w] > tin[v]:
                        boundary = sum((a in child) != (b in child) for a, b in edges)
                        if boundary == 2:
                            side = child if len(child)*2 < m else set(range(m))-child
                            cuts.add(tuple(sorted(side)))
            return subtree

        for v in range(m):
            if tin[v] < 0:
                dfs(v, -1)
    return cuts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-modulus', type=int, default=303)
    args = parser.parse_args()
    sys.setrecursionlimit(max(2000, args.max_modulus*3))
    rows = []
    for m in range(3, args.max_modulus+1, 6):
        actual = cuts_of_size_two(m)
        expected = {(m//3, 2*m//3)} if m % 9 == 0 else set()
        if actual != expected:
            raise AssertionError((m, actual, expected))
        rows.append({'modulus': m, 'cuts': sorted(actual)})
    print(json.dumps({'method': 'edge deletion plus multigraph bridges',
                      'moduli_checked': len(rows), 'failures': 0, 'results': rows}, indent=2))


if __name__ == '__main__':
    main()
