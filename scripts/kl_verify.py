#!/usr/bin/env python3
"""Independent re-verification of a saved multi-type certificate, in plain
Python integers with no numpy arithmetic (numpy is used only to load the
tables).  Re-derives every ingredient from scratch: classes, valuations,
child residues, lifts, shifts, and the cleared inequality

  W_j(r) * P^V * Q^E <= sum_i max_{j'} P^(V+e-v) Q^(E-e+v) * min_{lifts} W_{j'}

for every type j and fertile class r, plus the base bound.

    python3 scripts/kl_verify.py K J P Q vmax drops   e.g.  12 11 359 200 24 0,2,7,12
"""
import sys, math
import numpy as np

k, J, P, Q = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
vmax = int(sys.argv[5]); drops = set(int(x) for x in sys.argv[6].split(","))
W = np.load(f"scratch/kl_cert_{k}_{J}_{P}_{Q}.npy", allow_pickle=True)
W = [[int(x) for x in row] for row in W]
mod = 3 ** k; sub = 3 ** (k - 1)
fertile = [r for r in range(mod) if r % 3 != 0]
pos = {r: i for i, r in enumerate(fertile)}
assert len(W) == J + 1 and all(len(row) == len(fertile) for row in W)
L3 = math.log2(3)
opts = {j: [(jp, math.floor((j + 1 - jp) * L3 + 1e-12)) for jp in range(0, min(J, j + 1) + 1)
            if (j + 1 - jp) in drops] for j in range(J + 1)}
E = max(e for j in opts for (_, e) in opts[j]); V = vmax
lhs_coef = P ** V * Q ** E
coef = {}
def C(e, v):
    key = (e, v)
    if key not in coef:
        coef[key] = P ** (V + e - v) * Q ** (E - e + v)
    return coef[key]
def children(r):
    v0 = 2 if r % 3 == 1 else 1
    b = (2 ** v0 * r) % 9
    phase = 0 if b == 1 else (1 if b == 7 else 2)
    out = []
    j = 0
    while True:
        v = v0 + 2 * j
        if v > vmax: break
        if j % 3 != phase:
            m = (pow(2, v, mod) * r) % mod
            assert m % 3 == 1
            c = (m - 1) // 3
            out.append((v, c))
        j += 1
    return out
minrel = None; count = 0; bad = 0
for j in range(J + 1):
    for r in fertile:
        lhs = W[j][pos[r]] * lhs_coef
        rhs = 0
        for v, c in children(r):
            best = 0
            for jp, e in opts[j]:
                wbar = min(W[jp][pos[c]], W[jp][pos[c + sub]], W[jp][pos[c + 2 * sub]])
                t = C(e, v) * wbar
                if t > best: best = t
            rhs += best
        count += 1
        if rhs < lhs:
            bad += 1
            if bad <= 5: print("VIOLATION", j, r, lhs, rhs, flush=True)
        rel = (rhs - lhs) / lhs if lhs > 0 else float('inf')
        if minrel is None or rel < minrel: minrel = rel
        if W[j][pos[r]] <= 0:
            bad += 1; print("NONPOSITIVE", j, r, flush=True)
    print(f"type {j} done ({count} checked, {bad} bad)", flush=True)
wmax = max(max(row) for row in W); Kc = 1
while any(wmax * P ** y > Q ** y * Kc for y in range(23)): Kc *= 10
print(f"RESULT level {k} J {J} P/Q {P}/{Q}: inequalities checked {count}, violations {bad}, "
      f"min relative slack {minrel:.3e}, K = {Kc}, W_0(5) = {W[0][pos[5]]}, exponent {math.log2(P/Q):.4f}", flush=True)
