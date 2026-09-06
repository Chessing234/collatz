#!/usr/bin/env python3
"""Exact integer certificate for the multi-type absolute-bound scheme.

Inequality for type j, class r (cleared by P^V Q^E; V = vmax, E = max shift):
  W_j(r) * P^V * Q^E  <=  sum_i  max_{j'} [ P^(V+e-v_i) * Q^(E-e+v_i) * Wbar_{j'}(c_i) ]
with Wbar = min over the three lifts.  All checks below use Python integers
(numpy object arrays), so the certificate is exact.

    python3 scripts/kl_certify.py K J P Q [vmax] [iters] [scale]
Reports feasibility, min slack (relative), and writes tables to
scratch/kl_cert_K_J.npz when feasible.
"""
import sys, math, os
import numpy as np
from kl_levels import system
from kl_abs import growth_abs, L3

def build_opts(J, drops=None):
    opts = {}
    for j in range(J + 1):
        cand = list(range(0, min(J, j + 1) + 1))
        if drops is not None:
            cand = [jp for jp in cand if (j + 1 - jp) in drops]
        opts[j] = [(jp, math.floor((j + 1 - jp) * L3 + 1e-12)) for jp in cand]
    return opts

def float_tables(children, n, J, lam, iters, drops=None):
    W = np.ones((J + 1, n)); opts = build_opts(J, drops)
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
        W = nW / nW.sum()
    return W / W.max()

_COEF = {}

def coef_array(vi, P, Q, V, E, e):
    """P^(V+e-v) Q^(E-e+v) per element, cached per (e, distinct v)."""
    key = (P, Q, V, E, e)
    if key not in _COEF:
        _COEF[key] = {}
    table = _COEF[key]
    out = np.empty(len(vi), dtype=object)
    for vv in np.unique(vi):
        if int(vv) not in table:
            table[int(vv)] = P ** (V + e - int(vv)) * Q ** (E - e + int(vv))
        out[vi == vv] = table[int(vv)]
    return out

def exact_rhs(Wi, children, J, P, Q, V, E, opts):
    """RHS (object array, shape (J+1, n)) of the cleared inequalities."""
    n = Wi.shape[1]
    out = np.empty((J + 1, n), dtype=object)
    coefs = {}
    for j in range(J + 1):
        acc = np.zeros(n, dtype=object); acc[:] = 0
        for si, (v, lifts, ok) in enumerate(children):
            vi = v.astype(np.int64)
            best = np.zeros(n, dtype=object); best[:] = 0
            for jp, e in opts[j]:
                m = np.minimum(np.minimum(Wi[jp][lifts[0]], Wi[jp][lifts[1]]), Wi[jp][lifts[2]])
                if (si, e) not in coefs:
                    coefs[(si, e)] = coef_array(vi, P, Q, V, E, e)
                term = coefs[(si, e)] * m
                best = np.where(term > best, term, best)
            acc = acc + np.where(ok, best, 0)
        out[j] = acc
    return out

def certify(k, J, P, Q, vmax=24, iters=300, scale=10 ** 6, drops=None):
    n, children = system(k, vmax)
    lam = P / Q
    Wf = float_tables(children, n, J, lam, iters, drops)
    Wi = np.array([[int(x * scale) for x in row] for row in Wf], dtype=object)
    opts = build_opts(J, drops)
    E = max(e for j in opts for (_, e) in opts[j]); V = vmax
    lhs_coef = P ** V * Q ** E
    # decreasing repair: W <- min(W, floor(RHS / lhs_coef))
    for rep in range(50):
        rhs = exact_rhs(Wi, children, J, P, Q, V, E, opts)
        cap = np.array([[int(x) // lhs_coef for x in row] for row in rhs], dtype=object)
        newW = np.where(cap < Wi, cap, Wi)
        changed = int((newW != Wi).sum())
        Wi = newW
        print(f"  repair pass {rep}: {changed} entries lowered; min table {int(Wi.min())}", flush=True)
        if changed == 0:
            break
    fertile_pos = np.array([Wi[j].min() for j in range(J + 1)])
    feasible = all(int(Wi[j][i]) > 0 for j in range(J + 1) for i in range(n))
    rhs = exact_rhs(Wi, children, J, P, Q, V, E, opts)
    slack = rhs - Wi * lhs_coef
    minslack = min(int(x) for row in slack for x in row)
    rel = min(int(slack[j][i]) / (int(Wi[j][i]) * lhs_coef) for j in range(J + 1) for i in range(n))
    print(f"level {k}, J={J}, lambda={P}/{Q}=2^{math.log2(lam):.4f}: feasible={feasible}, "
          f"min slack {minslack} (relative {rel:.3e}), tables in [{int(Wi.min())}, {int(Wi.max())}]", flush=True)
    if feasible and minslack >= 0:
        # base bound: W_j(r) * P^y <= Q^y * K for y <= 22, K a power of ten
        wmax = int(Wi.max()); K = 1
        while any(wmax * P ** y > Q ** y * K for y in range(23)):
            K *= 10
        w0_5 = int(Wi[0][np.where(np.arange(3 ** k)[np.arange(3 ** k) % 3 != 0] == 5)[0][0]])
        print(f"  base bound: K = {K};  W_0(5) = {w0_5};  hence #reaching-1 up to N >= "
              f"({w0_5}/{K}) * (P/Q)^y with 10*2^y <= N, i.e. exponent log2(P/Q) = {math.log2(lam):.4f}", flush=True)
        os.makedirs("scratch", exist_ok=True)
        np.save(f"scratch/kl_cert_{k}_{J}_{P}_{Q}.npy", Wi.astype(object), allow_pickle=True)
    return feasible and minslack >= 0

if __name__ == "__main__":
    k, J, P, Q = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    vmax = int(sys.argv[5]) if len(sys.argv) > 5 else 24
    iters = int(sys.argv[6]) if len(sys.argv) > 6 else 300
    scale = int(sys.argv[7]) if len(sys.argv) > 7 else 10 ** 6
    drops = set(int(x) for x in sys.argv[8].split(",")) if len(sys.argv) > 8 else None
    certify(k, J, P, Q, vmax, iters, scale, drops)
