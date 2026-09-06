#!/usr/bin/env python3
"""Mechanism test for the 1/k law (Devices/StochasticTree.md §5).

At level k the certificate knows a root modulo 3^(k+1); the root's digit k+1
(delta in {0,1,2}) is what the min over lifts adversarially chooses.  That
digit shifts the residue mod 3 of every depth-k descendant by +delta or
-delta according to the parity of the descendant's total valuation V.  The
adversary gains from the IMBALANCE of those residues; if they were
equidistributed within each parity class, the shift would only permute them.

This script measures the imbalance directly, without the certificate: for
each root class r mod 3^(k+1) it propagates the weighted class vector of
descendants to depth k for each of the three lifts R = r + delta*3^(k+1)
(descendants at depth j are known mod 3^(k+2-j)), weights (3/2^v)^alpha per
edge, fertile children only, and reports the pi-weighted mean over r of

    (max_delta S(delta) - min_delta S(delta)) / mean_delta S(delta),

where S(delta) is the total weight of depth-k descendants that are fertile
(a residue-0 descendant is a leaf).  This is the one-generation gain the
adversary could extract at depth k from residues alone.  Also reported: the
same statistic for the weight of descendants ≡ 2 (mod 3), the "rich" residue.

    python3 scripts/tree_digits.py K [alpha] [vmax]
"""
import sys, math
import numpy as np

def step(vec_mod, mod, alpha, vmax):
    """vec_mod: weights on residues r mod `mod` (array of length mod, index = residue).
    Returns weights on child residues mod `mod // 3`."""
    sub = mod // 3
    out = np.zeros(sub)
    r = np.arange(mod)
    w = vec_mod
    live = w > 0
    for v in range(1, vmax + 1):
        m = (pow(2, v, mod) * r) % mod
        ok = live & (m % 3 == 1)
        if not ok.any():
            continue
        c = (m - 1) // 3          # residue mod sub
        np.add.at(out, c[ok], (3.0 / 2.0 ** v) ** alpha * w[ok])
    # children divisible by 3 are leaves: drop them
    cr = np.arange(sub)
    out[cr % 3 == 0] = 0.0
    return out

def imbalance(k, alpha, vmax):
    big = 3 ** (k + 2)
    base = 3 ** (k + 1)
    res = []
    rich = []
    for r in range(base):
        if r % 3 == 0:
            continue
        S = []; S2 = []
        for delta in range(3):
            vec = np.zeros(big); vec[r + delta * base] = 1.0
            mod = big
            for _ in range(k + 1):        # depth k+1 descendants are known mod 3
                vec = step(vec, mod, alpha, vmax); mod //= 3
            S.append(vec.sum()); S2.append(vec[2] if len(vec) > 2 else 0.0)
        S = np.array(S); S2 = np.array(S2)
        res.append((S.max() - S.min()) / S.mean() if S.mean() > 0 else 0.0)
        rich.append((S2.max() - S2.min()) / S2.mean() if S2.mean() > 0 else 0.0)
    return float(np.mean(res)), float(np.max(res)), float(np.mean(rich))

if __name__ == "__main__":
    k = int(sys.argv[1])
    alpha = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
    vmax = int(sys.argv[3]) if len(sys.argv) > 3 else 24
    mean_imb, max_imb, rich_imb = imbalance(k, alpha, vmax)
    print(f"k={k} alpha={alpha} | depth-{k+1} fertile-mass imbalance over the root's digit: "
          f"mean {mean_imb:.4f} max {max_imb:.4f} | residue-2 mass imbalance: mean {rich_imb:.4f} "
          f"| k*mean {k*mean_imb:.3f}", flush=True)
