#!/usr/bin/env python3
"""Two finer relaxations of the Krasikov--Lagarias min-over-lifts system, and
the concentration of its loss.

1. `coupled`: the three children of a parent class r (mod 3^k) do not choose
   their lifts independently -- all of them are fixed by the parent's next
   3-adic digit delta.  So  F(w)_r = min_delta sum_v (3/2^v)^alpha w(c_v(r + delta 3^k) mod 3^k)
   is sound, dominates the K-L sum-of-mins, and is the level-(k+1) system
   restricted to weights constant on lifts.  Same number of unknowns as level k.

2. `loss`: with w the K-L Perron vector at alpha_k and pi the stationary law of
   the averaged map, the per-class loss  pi(r) * (avg_lifts - min_lifts)/avg  is
   tabulated and its concentration (share of total loss carried by the top
   1%, 5%, 20% of classes) reported.  If concentrated, adaptive refinement of
   those classes is the cheap way to a higher exponent.

    python3 scripts/kl_relax.py K [vmax] [iters]
"""
import sys, math
import numpy as np
from kl_levels import system
from kl_spectrum import growth, exponent, stationary

def coupled_system(k, vmax):
    """Children of the level-(k+1) lifts of each level-k class, mapped back to
    level-k classes.  Returns n, and for each delta a list of (v, idx, ok)."""
    mod, big = 3 ** k, 3 ** (k + 1)
    r = np.arange(mod)
    fertile = np.where(r % 3 != 0)[0]
    n = len(fertile)
    pos = -np.ones(mod, dtype=np.int64); pos[fertile] = np.arange(n)
    v0 = np.where(fertile % 3 == 1, 2, 1)
    base = ((2 ** v0) * fertile) % 9
    phase = np.where(base == 1, 0, np.where(base == 7, 1, 2))
    jmax = (vmax - 1) // 2 + 1
    per_delta = []
    for delta in range(3):
        R = fertile.astype(np.int64) + delta * mod
        lst = []
        for j in range(jmax):
            v = v0 + 2 * j
            ok = (j % 3 != phase) & (v <= vmax)
            if not ok.any():
                continue
            m = ((np.left_shift(np.int64(1), v.astype(np.int64)) % big) * R) % big
            c = (m - 1) // 3            # child class mod 3^k, fertile where ok
            idx = pos[np.where(ok, c, fertile[0])].astype(np.int64)
            lst.append((v.astype(np.uint8), idx, ok))
        per_delta.append(lst)
    return n, per_delta

def coupled_growth(per_delta, n, alpha, iters=300, window=40):
    w = np.ones(n); logs = []
    for _ in range(iters):
        best = None
        for lst in per_delta:
            s = np.zeros(n)
            for v, idx, ok in lst:
                s += np.where(ok, (3.0 / 2.0 ** v.astype(np.float64)) ** alpha * w[idx], 0.0)
            best = s if best is None else np.minimum(best, s)
        logs.append(math.log(best.sum() / w.sum()))
        w = best / best.sum()
    return math.exp(sum(logs[-window:]) / window)

def coupled_exponent(per_delta, n, iters, lo=0.3, hi=1.0, steps=20):
    for _ in range(steps):
        mid = (lo + hi) / 2
        if coupled_growth(per_delta, n, mid, iters) >= 1.0:
            lo = mid
        else:
            hi = mid
    return lo

def loss_profile(k, children, n, alpha, iters):
    _, w = growth(children, n, alpha, 'min', iters, return_vec=True)
    pi = stationary(children, n, iters)
    mod, sub = 3 ** k, 3 ** (k - 1)
    fertile = np.arange(mod)[np.arange(mod) % 3 != 0]
    # loss at parent class r: sum over children of weight*(avg - min)/avg of lifts of w
    loss = np.zeros(n); tot = np.zeros(n)
    for v, lifts, ok in children:
        a, b, c = w[lifts[0]], w[lifts[1]], w[lifts[2]]
        avg = (a + b + c) / 3; mn = np.minimum(np.minimum(a, b), c)
        wt = np.where(ok, (3.0 / 2.0 ** v.astype(np.float64)) ** alpha, 0.0)
        loss += wt * (avg - mn); tot += wt * avg
    rel = loss / np.maximum(tot, 1e-300)
    contrib = pi * rel
    order = np.argsort(-contrib)
    cs = np.cumsum(contrib[order]) / contrib.sum()
    shares = {p: float(cs[max(int(p * n) - 1, 0)]) for p in (0.01, 0.05, 0.2, 0.5)}
    top = fertile[order[:12]]
    return float((pi * rel).sum()), shares, top, rel[order[:12]]

if __name__ == "__main__":
    k = int(sys.argv[1])
    vmax = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    n, children = system(k, vmax)
    a_k = exponent(children, n, 'min', iters)
    nc, per_delta = coupled_system(k, vmax)
    a_c = coupled_exponent(per_delta, nc, iters)
    r_c = coupled_growth(per_delta, nc, 1.0, iters)
    mean_loss, shares, top, toprel = loss_profile(k, children, n, a_k, iters)
    print(f"k={k} n={n} | alpha_k {a_k:.5f} | coupled: alpha {a_c:.5f} rho(1) {r_c:.5f} "
          f"| pi-mean loss {mean_loss:.4f} | loss share top1% {shares[0.01]:.3f} top5% {shares[0.05]:.3f} "
          f"top20% {shares[0.2]:.3f} top50% {shares[0.5]:.3f}", flush=True)
    print("   worst classes (r mod 3^k, rel loss):", [(int(r), round(float(x), 3)) for r, x in zip(top, toprel)], flush=True)
