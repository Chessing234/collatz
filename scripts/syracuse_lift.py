#!/usr/bin/env python3
"""The Syracuse random variable as a Krasikov--Lagarias test vector.

Background (Devices/StochasticTree.md, Theorem A): the lift-averaged K-L
transfer at exponent 1 is A_1 = P^T for the Haar-random forward Syracuse
chain on Z/3^(k+1), so rho(A_1) = 1 and the whole gap to exponent 1 is the
min-over-lifts relaxation.

This script identifies the Perron vector of A_1 explicitly.  Let

    mu_n := law of  S_n = sum_{m=1}^{n} 3^(m-1) 2^(-(a_1+...+a_m))  mod 3^n,
    a_i iid geometric, P(a = j) = 2^(-j), j >= 1

-- Tao's Syracuse random variable Syrac(Z/3^n) (Forum Math Pi 10 (2022), §1.3).
It satisfies mu_n = law of 2^(-a) (3 Y + 1) mod 3^n with Y ~ mu_(n-1), hence

    mu_(k+1)(r) = sum_v 2^(-v) mu_k(childClass k v r)                     (*)

which is exactly  A_1 mu_(k+1) = mu_(k+1):  the stationary law of the forward
chain IS the K-L Perron vector at exponent 1.

Consequence (the point of this script).  Put

    beta_n := 3 * min over fertile c mod 3^(n-1), j < 3  of
                  mu_n(c + j 3^(n-1)) / mu_(n-1)(c) ,

the worst relative share of a class mod 3^(n-1) taken by one of its three
lifts mod 3^n -- the L^inf lift-discrepancy of the Syracuse random variable.
Using mu_(k+1) as a K-L test vector, min >= (beta/3) * (sum over lifts) gives

    rho_k(1) >= beta_(k+1)                                              (**)

and more generally a certified exponent alpha whenever
beta_(k+1) * min_r F_r(alpha) >= 1 with
F_r(alpha) = sum_v t_v^alpha mu_k(c_v) / sum_v t_v mu_k(c_v), t_v = 3/2^v.

So: if the Syracuse random variable equidistributes over lifts in L^inf,
the K-L exponents tend to 1 -- unconditionally, with no hypothesis about the
tree of 1.  Usage:  python3 scripts/syracuse_lift.py NMAX [vmax]
"""
import sys
import numpy as np


def syracuse_laws(nmax, A=64):
    """mu_1 .. mu_nmax as float64 arrays, mu_n indexed by residue mod 3^n."""
    laws = []
    mu = np.zeros(3, dtype=np.float64)
    # S_1 = 2^(-a_1): residue 1 if a even, 2 if a odd
    for a in range(1, A + 1):
        mu[pow(2, -a, 3)] += 2.0 ** (-a)          # S_1 = 2^(-a_1) mod 3
    mu /= mu.sum()
    laws.append(mu)
    for n in range(2, nmax + 1):
        M = 3 ** n
        prev = laws[-1]
        Mp = 3 ** (n - 1)
        y = np.arange(Mp, dtype=np.int64)
        base = (3 * y + 1) % M
        out = np.zeros(M, dtype=np.float64)
        inv = pow(2, -1, M)
        f = 1
        for a in range(1, A + 1):
            f = f * inv % M
            idx = (base * f) % M
            out[idx] += (2.0 ** (-a)) * prev
        out /= out.sum()
        laws.append(out)
    return laws


def report(nmax, A=64):
    laws = syracuse_laws(nmax, A)
    print(f"{'n':>3} {'proj err':>10} {'beta_n':>10} {'gamma_n':>10} "
          f"{'n(1-beta)':>10} {'meanosc':>9} {'minmass*3^n':>12}")
    betas = {}
    for n in range(2, nmax + 1):
        mu, prev = laws[n - 1], laws[n - 2]
        L = mu.reshape(3, 3 ** (n - 1))          # lifts c + j*3^(n-1)
        proj = L.sum(axis=0)
        err = np.abs(proj - prev).max()
        fert = prev > 0
        share = np.zeros_like(L)
        share[:, fert] = 3.0 * L[:, fert] / prev[fert]
        beta = share[:, fert].min()
        gamma = share[:, fert].max()
        osc = ((share[:, fert].max(axis=0) - share[:, fert].min(axis=0)) * prev[fert]).sum()
        betas[n] = beta
        print(f"{n:>3} {err:10.2e} {beta:10.6f} {gamma:10.6f} "
              f"{n * (1 - beta):10.4f} {osc:9.5f} {mu.min() * 3 ** n:12.4e}")
    return laws, betas


if __name__ == '__main__':
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    A = int(sys.argv[2]) if len(sys.argv) > 2 else 64
    report(nmax, A)
