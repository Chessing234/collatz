#!/usr/bin/env python3
"""mu_(k+1) (Tao's Syracuse random variable) as an explicit K-L test vector.

For level k the K-L min-system is
    (F_alpha W)(r) = sum_v (3/2^v)^alpha * min_{j<3} W(c_v(r) + j*3^k),
    c_v(r) = ((2^v r mod 3^(k+1)) - 1)/3,  admissible v: 2^v r = 1 mod 3.
Theorem A: replacing min by the average gives A_alpha, and A_1 mu = mu with
mu = mu_(k+1) the law of Syrac(Z/3^(k+1)).  Hence, writing
    s(c) := 3 * min_j mu_(k+1)(c + j 3^k) / mu_k(c)      (the min lift share)
one gets the *unconditional* test-vector bound
    rho_k(1) >= min_r  sum_v 2^(-v) mu_k(c_v(r)) s(c_v(r)) / mu_(k+1)(r)
which is a mu-weighted average of shares, not their global minimum.
This script computes that bound, the exponent it certifies, and (for small k)
the true growth of the min-system for comparison.
"""
import sys, math
import numpy as np
from syracuse_lift import syracuse_laws

A = 64

def level(k, laws):
    """admissible (v, c_v) data for classes r mod 3^(k+1)."""
    M = 3 ** (k + 1)
    r = np.arange(M, dtype=np.int64)
    out = []
    p = 1
    for v in range(1, A + 1):
        p = p * 2 % M
        y = (r * p) % M
        ok = (y % 3 == 1)
        cv = np.where(ok, (y - 1) // 3, 0)
        out.append((v, cv, ok))
    return out

def bound(k, laws):
    mu1, mu0 = laws[k], laws[k - 1]        # mu_(k+1) on 3^(k+1), mu_k on 3^k
    L = mu1.reshape(3, 3 ** k)
    fert = mu0 > 0
    s = np.zeros(3 ** k)
    s[fert] = 3.0 * L[:, fert].min(axis=0) / mu0[fert]
    num = np.zeros(3 ** (k + 1)); den = np.zeros(3 ** (k + 1))
    for v, cv, ok in level(k, laws):
        w = np.where(ok, 2.0 ** (-v) * mu0[cv], 0.0)
        num += w * np.where(ok, s[cv], 0.0)
        den += w
    live = mu1 > 0
    ratio = num[live] / den[live]
    return ratio.min(), s

def certified_alpha(k, laws, s):
    """largest alpha with  min_r sum_v t_v^a mu_k(c_v) s(c_v) / mu_(k+1)(r) >= 1."""
    mu1, mu0 = laws[k], laws[k - 1]
    data = level(k, laws)
    live = mu1 > 0
    def g(a):
        num = np.zeros(3 ** (k + 1))
        for v, cv, ok in data:
            t = (3.0 / 2.0 ** v) ** a
            num += np.where(ok, t * mu0[cv] * s[cv], 0.0)
        return (num[live] / (3.0 * mu1[live])).min()
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if g(mid) >= 1.0: lo = mid
        else: hi = mid
    return lo

def true_rho(k, laws, iters=400):
    data = level(k, laws)
    M = 3 ** (k + 1)
    w = np.ones(M); w[laws[k] == 0] = 0.0
    logs = []
    for _ in range(iters):
        nw = np.zeros(M)
        W = w.reshape(3, 3 ** k)
        m = W.min(axis=0)
        for v, cv, ok in data:
            nw += np.where(ok, (3.0 / 2.0 ** v) * m[cv], 0.0)
        sset = nw.sum()
        logs.append(math.log(sset / w.sum())); w = nw / sset
    return math.exp(sum(logs[-40:]) / 40)

if __name__ == '__main__':
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    laws = syracuse_laws(kmax + 1, A)
    print(f"{'k':>3} {'mu-bound':>10} {'alpha(mu)':>10} {'rho_k(1)':>10} {'beta_(k+1)':>11}")
    for k in range(1, kmax + 1):
        b, s = bound(k, laws)
        a = certified_alpha(k, laws, s)
        tr = true_rho(k, laws) if k <= 9 else float('nan')
        beta = s[laws[k - 1] > 0].min()
        print(f"{k:>3} {b:10.6f} {a:10.6f} {tr:10.6f} {beta:11.6f}")
