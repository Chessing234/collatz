#!/usr/bin/env python3
"""How far must you look before a node's subtree covers every class mod 3^k?

`Strategy/BackwardMixing.backward_mixing` proves that ONE generation covers
every class mod 3^k exactly once -- but only over a full period of 3^k slots,
which costs valuation 2*3^k, i.e. scale 4^(3^k).  Exponential.  The subtree
does far better, and how much better is the mechanism behind the 1/k law of
`Devices/StochasticTree.md`.  Two measurements, both best-first searches from
a root a over its actual inverse-Syracuse descendants:

  * `valuation`: least total valuation V with all fertile classes mod 3^k hit.
    Measured  V ~ 5k  (against 2*3^k for one generation).
  * `scale`   : least X with all fertile classes mod 3^k hit below X.
    Measured  X / a = Theta(M log M),  M = 3^k -- the coupon-collector scale
    for a set of counting exponent 1, equidistributed mod M.

So the tree's 3-adic covering is exactly as fast as a density-one
equidistributed set would manage: no 3-adic obstruction is visible at the
level of covering.  The obstruction is in the multiplicities, not the support.

    python3 scripts/backward_cover.py [scale|valuation] [kmax]
"""
import heapq, math, sys


def children(n, slots):
    v0 = 1 if n % 3 == 2 else 2
    out = []
    for j in range(slots):
        c = (2 ** (v0 + 2 * j) * n - 1) // 3
        if c % 3:
            out.append((v0 + 2 * j, c))
    return out


def cover(a, k, by, cap=6_000_000, slots=24, ceiling=10 ** 30):
    """least total valuation (by='valuation') or least X (by='scale') covering
    every fertile class mod 3^k in the subtree of a."""
    m = 3 ** k
    need = {r for r in range(m) if r % 3}
    seen, cnt = set(), 0
    pq = [(0, a)] if by == 'valuation' else [a]
    while pq and need and cnt < cap:
        if by == 'valuation':
            cost, n = heapq.heappop(pq)
        else:
            n = heapq.heappop(pq); cost = n
        if n in seen:
            continue
        seen.add(n); cnt += 1
        need.discard(n % m)
        if not need:
            return cost, cnt
        for v, c in children(n, slots):
            if c > ceiling:
                break
            heapq.heappush(pq, (cost + v, c) if by == 'valuation' else c)
    return None, cnt


if __name__ == '__main__':
    by = sys.argv[1] if len(sys.argv) > 1 else 'scale'
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    roots = (1, 7, 1234567, 99999999977)
    if by == 'valuation':
        print(f"{'a':>12} {'k':>2} {'#classes':>9} {'minV':>6} {'2*3^k':>8} {'nodes':>8}")
    else:
        print(f"{'a':>12} {'k':>2} {'M=3^k':>7} {'X/a':>12} {'X/(a M lnM)':>12} "
              f"{'log_M(X/a)':>11} {'nodes':>8}")
    for a in roots:
        for k in range(1, kmax + 1):
            c, cnt = cover(a, k, by)
            if c is None:
                print(f"{a:>12} {k:>2}  incomplete ({cnt} nodes)"); continue
            if by == 'valuation':
                print(f"{a:>12} {k:>2} {2*3**(k-1):>9} {c:>6} {2*3**k:>8} {cnt:>8}")
            else:
                M = 3 ** k
                print(f"{a:>12} {k:>2} {M:>7} {c/a:>12.1f} "
                      f"{(c/a)/(M*math.log(M)) if k > 0 else 0:>12.3f} "
                      f"{math.log(c/a)/math.log(M) if c > a else float('nan'):>11.3f} {cnt:>8}")
