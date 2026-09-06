#!/usr/bin/env python3
"""Per-root 3-adic balance of the inverse tree: the computable shadow of G8.

`Equi` (Strategy/TreeBalance9) is about the tree of 1, which below 10^9 is
every integer, so it cannot be tested directly.  The subtree of one large root
IS a genuine thin inverse-closed set, and its balance is exactly what the
per-root absolute-bound induction would need (Devices/StochasticTree.md sec 5,
sketch 3).  This enumerates the descendants of a root a below a*Y and reports
the spread of their classes mod 3, 9, 27.

    python3 scripts/tree_perroot.py [kmax] [Ymax_exponent]
"""
import sys

def counts_mod(a, Y, k):
    m, X = 3 ** k, a * Y
    cnt = [0] * m
    stack, tot = [a], 0
    while stack:
        n = stack.pop()
        v = 1 if n % 3 == 2 else 2
        while True:
            c = (2 ** v * n - 1) // 3
            if c > X:
                break
            if c % 3 and c != n:          # c == n only at the fixed point 1
                cnt[c % m] += 1
                tot += 1
                stack.append(c)
            v += 2
    return cnt, tot

def fold(cnt, k, j):
    """counts mod 3^k folded down to mod 3^j"""
    m = 3 ** j
    out = [0] * m
    for r, c in enumerate(cnt):
        out[r % m] += c
    return out

if __name__ == '__main__':
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    E = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    roots = [int(x) for x in sys.argv[3:]] or [1, 25, 1234567, 99999999977]
    for a in roots:
        assert a % 2 == 1 and a % 3 != 0, f'root {a} must be odd and prime to 3'
        print(f"root a = {a}")
        print(f"  {'Y':>9} {'nodes':>9} " +
              " ".join(f"{'min/max mod 3^'+str(j)+' chi':>26}" for j in range(1, K + 1)))
        for e in range(2, E + 1):
            Y = 10 ** e
            cnt, tot = counts_mod(a, Y, K)
            if tot == 0:
                continue
            cells = []
            for j in range(1, K + 1):
                c = fold(cnt, K, j)
                vals = [c[r] for r in range(3 ** j) if r % 3]
                mean = tot / len(vals)
                chi = max(abs(v - mean) for v in vals) / mean ** 0.5
                cells.append(f"{min(vals)/mean:6.4f}/{max(vals)/mean:<6.4f} chi{chi:5.2f}")
            print(f"  {Y:>9} {tot:>9} " + " ".join(cells), flush=True)
