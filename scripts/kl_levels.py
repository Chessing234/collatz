#!/usr/bin/env python3
"""Continuous Krasikov--Lagarias residue-class system, vectorised.

Classes: fertile residues r mod 3^k (odd-only formulation of TreeBranching).
A parent of class r has fertile children at valuations v = v0 + 2j
(j != phase mod 3), of size ~ 2^v r / 3; the child's class mod 3^(k-1) is
c(r, v) = ((2^v r) mod 3^k - 1)/3, and its weight is the MINIMUM of w over the
three lifts of c.  The exponent alpha is certified iff the monotone homogeneous
map F_alpha(w)_r = sum_v (3/2^v)^alpha * min_{lifts} w has growth rate >= 1.
Growth rate = geometric mean of the total-mass ratio over the last iterations.

    python3 scripts/kl_levels.py K [vmax] [iters]
"""
import sys, math
import numpy as np

def system(k, vmax):
    mod = 3 ** k
    sub = 3 ** (k - 1)
    r = np.arange(mod)
    fertile = np.where(r % 3 != 0)[0]
    n = len(fertile)
    pos = -np.ones(mod, dtype=np.int64)
    pos[fertile] = np.arange(n)
    v0 = np.where(fertile % 3 == 1, 2, 1)
    base = ((2 ** v0) * fertile) % 9
    phase = np.where(base == 1, 0, np.where(base == 7, 1, 2))
    children = []   # list of (v_array, lift index arrays (3, n))
    # valuations v = v0 + 2j, j = 0.. while v <= vmax, skipping j == phase mod 3
    jmax = (vmax - 1) // 2 + 1
    for j in range(jmax):
        v = v0 + 2 * j
        ok = (j % 3 != phase) & (v <= vmax)
        if not ok.any():
            continue
        # 2^v r mod 3^k: v <= vmax <= 24 and mod <= 3^13, so the product fits int64
        m = ((np.left_shift(np.int64(1), v.astype(np.int64)) % mod) * fertile.astype(np.int64)) % mod
        c = (m - 1) // 3          # residue mod 3^(k-1), fertile
        lifts = np.stack([pos[c], pos[c + sub], pos[c + 2 * sub]]).astype(np.int32)   # (3, n)
        children.append((v.astype(np.uint8), lifts, ok))
        del m, c
    return n, children

def growth(children, n, alpha, iters=300, window=40):
    w = np.ones(n)
    logs = []
    for it in range(iters):
        nw = np.zeros(n)
        for v, lifts, ok in children:
            m = np.minimum(np.minimum(w[lifts[0]], w[lifts[1]]), w[lifts[2]])
            nw += np.where(ok, (3.0 / 2.0 ** v.astype(np.float64)) ** alpha * m, 0.0)
        tot_old = w.sum(); tot_new = nw.sum()
        logs.append(math.log(tot_new / tot_old))
        w = nw / tot_new
    return math.exp(sum(logs[-window:]) / window)

def exponent(k, vmax=24, iters=300, lo=0.3, hi=1.0, steps=18):
    n, children = system(k, vmax)
    for _ in range(steps):
        mid = (lo + hi) / 2
        if growth(children, n, mid, iters) >= 1.0:
            lo = mid
        else:
            hi = mid
    return lo, n

if __name__ == "__main__":
    k = int(sys.argv[1])
    vmax = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    a, n = exponent(k, vmax, iters)
    print(f"K-L continuous system, classes mod 3^{k} ({n} classes), vmax {vmax}: exponent {a:.4f}", flush=True)
