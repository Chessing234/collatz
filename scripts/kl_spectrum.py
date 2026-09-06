#!/usr/bin/env python3
"""Spectral diagnostics of the Krasikov--Lagarias class system, level by level.

Three monotone homogeneous maps on the fertile classes r mod 3^k share the
same structure  F(w)_r = sum_v (3/2^v)^alpha * AGG_{lifts of c(r,v)} w :

    min  -- the K-L certificate (sound lower bound, `kl_levels.py`);
    avg  -- the lift-averaged system;
    max  -- the mirror (would give an upper bound on subtree counts).

Fact (checked here in floating point, proved in Strategy/TreeStochastic):
at alpha = 1 the avg map is a column-stochastic linear map, so its growth
rate is exactly 1 at every level.  Hence the entire gap between the K-L
exponent alpha_k and 1 is the min-over-lifts relaxation.  This script measures
that gap three ways:

  * rho_k(1): growth rate of the min map at alpha = 1  (1 - rho is the loss);
  * alpha_k : the K-L exponent (growth rate 1), bisected;
  * osc_k   : the lift oscillation of the K-L weights at alpha_k, i.e. the
              pi-weighted mean of (max - min)/mean over the three lifts of each
              class mod 3^(k-1), where pi is the stationary law of the avg map.

    python3 scripts/kl_spectrum.py K [vmax] [iters]
"""
import sys, math
import numpy as np
from kl_levels import system

def apply(children, w, alpha, agg):
    nw = np.zeros_like(w)
    for v, lifts, ok in children:
        a, b, c = w[lifts[0]], w[lifts[1]], w[lifts[2]]
        if agg == 'min':
            m = np.minimum(np.minimum(a, b), c)
        elif agg == 'max':
            m = np.maximum(np.maximum(a, b), c)
        else:
            m = (a + b + c) / 3.0
        nw += np.where(ok, (3.0 / 2.0 ** v.astype(np.float64)) ** alpha * m, 0.0)
    return nw

def growth(children, n, alpha, agg, iters=300, window=40, return_vec=False):
    w = np.ones(n)
    logs = []
    for _ in range(iters):
        nw = apply(children, w, alpha, agg)
        logs.append(math.log(nw.sum() / w.sum()))
        w = nw / nw.sum()
    g = math.exp(sum(logs[-window:]) / window)
    return (g, w) if return_vec else g

def exponent(children, n, agg, iters, lo=0.3, hi=1.2, steps=20):
    for _ in range(steps):
        mid = (lo + hi) / 2
        if growth(children, n, mid, agg, iters) >= 1.0:
            lo = mid
        else:
            hi = mid
    return lo

def stationary(children, n, iters):
    """Left Perron vector of the avg map at alpha = 1 (column-stochastic, so
    this is the stationary law of the Haar-random Syracuse chain on classes)."""
    # transpose action: pi_new[r'] = sum over (r, v) with r' a lift of c(r,v) of (3/2^v)/3 * pi[r]
    pi = np.ones(n) / n
    for _ in range(iters):
        npi = np.zeros(n)
        for v, lifts, ok in children:
            wgt = np.where(ok, (3.0 / 2.0 ** v.astype(np.float64)) / 3.0 * pi, 0.0)
            for i in range(3):
                np.add.at(npi, lifts[i], wgt)
        pi = npi / npi.sum()
    return pi

def lift_oscillation(k, w, pi):
    """Group the fertile classes mod 3^k by their residue mod 3^(k-1); the
    three members of a group are the lifts.  Returns pi-weighted and plain
    means of (max-min)/mean over groups."""
    mod, sub = 3 ** k, 3 ** (k - 1)
    fertile = np.arange(mod)[np.arange(mod) % 3 != 0]
    grp = fertile % sub
    order = np.argsort(grp, kind='stable')
    W = w[order].reshape(-1, 3); P = pi[order].reshape(-1, 3)
    osc = (W.max(1) - W.min(1)) / W.mean(1)
    pw = P.sum(1)
    return float((osc * pw).sum() / pw.sum()), float(osc.mean()), float(osc.max())

if __name__ == "__main__":
    k = int(sys.argv[1])
    vmax = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    n, children = system(k, vmax)
    r_avg = growth(children, n, 1.0, 'avg', iters)
    r_min, wmin1 = growth(children, n, 1.0, 'min', iters, return_vec=True)
    r_max = growth(children, n, 1.0, 'max', iters)
    a_min = exponent(children, n, 'min', iters)
    a_max = exponent(children, n, 'max', iters)
    _, w_at = growth(children, n, a_min, 'min', iters, return_vec=True)
    pi = stationary(children, n, iters)
    osc_w, osc_p, osc_x = lift_oscillation(k, w_at, pi)
    osc1_w, osc1_p, osc1_x = lift_oscillation(k, wmin1, pi)
    print(f"k={k} n={n} vmax={vmax} | rho(1): avg {r_avg:.7f} min {r_min:.6f} max {r_max:.6f} "
          f"| alpha: min {a_min:.5f} max {a_max:.5f} "
          f"| osc@alpha_k: pi-wtd {osc_w:.4f} plain {osc_p:.4f} max {osc_x:.4f} "
          f"| osc@1: pi-wtd {osc1_w:.4f} plain {osc1_p:.4f} max {osc1_x:.4f}", flush=True)
