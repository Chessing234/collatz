#!/usr/bin/env python3
"""Multi-type absolute-bound scheme (the induction of Strategy/TreeTwoThirds
generalised to J+1 scale types 3^j 2^y a), vectorised.

Claim types j = 0..J.  From type j a child at valuation v has exact bound
3^(j+1) 2^(y-v) c and may use any type j' <= min(J, j+1) at index
y' = y - v + e(j, j'),  e = floor((j+1-j') log2 3),  weight lam^(e - v).
Induction on the absolute bound makes every option available.

    python3 scripts/kl_abs.py K J lam [vmax] [iters]     # growth rate at lam
    python3 scripts/kl_abs.py K J exp [vmax] [iters]     # bisect the exponent
"""
import sys, math
import numpy as np
from kl_levels import system

L3 = math.log2(3)

def growth_abs(children, n, J, lam, iters=300, window=40, drops=None):
    # W shape (J+1, n)
    W = np.ones((J + 1, n))
    logs = []
    opts = {}
    for j in range(J + 1):
        cand = list(range(0, min(J, j + 1) + 1))
        if drops is not None:
            cand = [jp for jp in cand if (j + 1 - jp) in drops]
        opts[j] = [(jp, math.floor((j + 1 - jp) * L3 + 1e-12)) for jp in cand]
    for it in range(iters):
        nW = np.zeros_like(W)
        for j in range(J + 1):
            acc = np.zeros(n)
            for v, lifts, ok in children:
                best = np.zeros(n)
                for jp, e in opts[j]:
                    m = np.minimum(np.minimum(W[jp][lifts[0]], W[jp][lifts[1]]), W[jp][lifts[2]])
                    np.maximum(best, lam ** (e - v) * m, out=best)
                acc += np.where(ok, best, 0.0)
            nW[j] = acc
        tot_old = W.sum(); tot_new = nW.sum()
        logs.append(math.log(tot_new / tot_old))
        W = nW / tot_new
    return math.exp(sum(logs[-window:]) / window)

def exponent_abs(k, J, vmax=24, iters=300, drops=None):
    n, children = system(k, vmax)
    lo, hi = 1.0, 2.0
    for _ in range(16):
        mid = (lo + hi) / 2
        if growth_abs(children, n, J, mid, iters, drops=drops) >= 1.0:
            lo = mid
        else:
            hi = mid
    return math.log2(lo), n

if __name__ == "__main__":
    k = int(sys.argv[1]); J = int(sys.argv[2]); what = sys.argv[3]
    vmax = int(sys.argv[4]) if len(sys.argv) > 4 else 24
    iters = int(sys.argv[5]) if len(sys.argv) > 5 else 300
    if what == "exp":
        a, n = exponent_abs(k, J, vmax, iters)
        print(f"abs scheme, classes mod 3^{k} ({n}), J = {J}: exponent {a:.4f}", flush=True)
    else:
        lam = float(what)
        n, children = system(k, vmax)
        g = growth_abs(children, n, J, lam, iters)
        print(f"abs scheme, classes mod 3^{k} ({n}), J = {J}, lambda {lam} (2^{math.log2(lam):.4f}): growth {g:.5f}", flush=True)
