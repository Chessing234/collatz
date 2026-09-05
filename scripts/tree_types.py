#!/usr/bin/env python3
"""Exponent certified by the Krasikov--Lagarias residue-class system, in the
odd-only formulation of Strategy/TreeBranching.

For a fertile root a (odd, prime to 3) let S(a, Y) count the odd fertile n <= Y
whose orbit passes through a.  The i-th fertile child of a sits at valuation
v = v0 + 2j (j not congruent to phase mod 3) and has size ~ 2^v a / 3, so

    S(a, Y) >= sum_v S(child_v, Y),   S(child_v, Y) ~ w(class of child) (Y / child)^alpha.

The child's class modulo 3^(k-1) is decided by a modulo 3^k; its class modulo
3^k is not.  Krasikov--Lagarias make the bound class-uniform: the weight used
for the child is the MINIMUM over its three lifts.  Then

    w_r <= sum_v (3 / 2^v)^alpha * min_{r' lifts c(r, v)} w_{r'}          (*)

must admit a positive solution w, and the certified exponent is the largest
alpha for which the monotone homogeneous map F_alpha(w)_r = RHS of (*) has
growth rate >= 1.

The child at v = 1 is SMALLER than a, so its term is "advanced" (its relative
scale exceeds the parent's); a plain induction on scale cannot use it.
`truncated=True` drops it (Applegate--Lagarias); `truncated=False` keeps it
(sound only with the Krasikov--Lagarias elimination theorem).

    python3 scripts/tree_types.py [kmax] [vmax]
"""
import sys

def classes(k):
    mod = 3 ** k
    return mod, [r for r in range(mod) if r % 3 != 0]

def children(r, k, vmax, mode):
    """List of (charged valuation, child class mod 3^(k-1)) for the fertile
    children of class r.  mode: 'drop' omits the v = 1 child (Applegate--
    Lagarias truncation); 'charge2' keeps it but charges it as if at v = 2,
    which is sound (its size is below 4a/3 < 2^2 a / 3) and retarded;
    'full' keeps it at its true size (needs the K--L elimination theorem).
    Requires k >= 2 so that the phase is decided by r."""
    mod = 3 ** k
    v0 = 2 if r % 3 == 1 else 1
    base = (2 ** v0 * r) % 9
    phase = 0 if base == 1 else (1 if base == 7 else 2)
    out = []
    for j in range(0, (vmax - v0) // 2 + 1):
        if j % 3 == phase:
            continue
        v = v0 + 2 * j
        s = (2 ** v * r) % mod
        c = (s - 1) // 3
        if v == 1 and mode == 'drop':
            continue
        vc = 2 if (v == 1 and mode == 'charge2') else v
        out.append((vc, c % (3 ** (k - 1))))
    return out

def growth(k, alpha, vmax, mode, iters=400):
    mod, types = classes(k)
    idx = {r: i for i, r in enumerate(types)}
    sub = 3 ** (k - 1)
    lifts = {c: [r for r in types if r % sub == c] for c in range(sub)}
    ch = {r: children(r, k, vmax, mode) for r in types}
    w = [1.0] * len(types)
    rate = 1.0
    for _ in range(iters):
        nw = []
        for r in types:
            tot = 0.0
            for v, c in ch[r]:
                m = min(w[idx[rr]] for rr in lifts[c])
                tot += (3.0 / 2 ** v) ** alpha * m
            nw.append(tot)
        rate = max(nw)
        w = [x / rate for x in nw]
    return rate

def exponent(k, vmax, mode):
    lo, hi = 0.05, 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if growth(k, mid, vmax, mode) >= 1.0:
            lo = mid
        else:
            hi = mid
    return lo

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    vmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    print(f"vmax = {vmax}")
    for k in range(2, kmax + 1):
        a_d = exponent(k, vmax, 'drop')
        a_c = exponent(k, vmax, 'charge2')
        a_f = exponent(k, vmax, 'full')
        print(f"classes mod 3^{k} ({len(classes(k)[1]):4d} classes): "
              f"drop v=1 {a_d:.4f}   charge v=1 at v=2 {a_c:.4f}   full {a_f:.4f}")

# ---------------------------------------------------------------------------
# The two-type lattice system actually used in Strategy/TreeBranching-style
# inductions.  Claims: F_r(y): S(a, 2^y a) >= A_r lam^y and H_r(y):
# S(a, 3 2^y a) >= B_r lam^y for every root a of class r.  At index y prove
# F(y) first (children at H(y - v), all retarded), then H(y) (children at
# H(y - v + 1) for v >= 2, and the v = 1 child at F(y), already proved).
#   A_r <= sum_v lam^{-v} Bbar_{c(r,v)}
#   B_r <= [v=1 fertile] Abar_{c(r,1)} + sum_{v>=2} lam^{1-v} Bbar_{c(r,v)}
# where bar = min over the three lifts of the child's class.

def growth_lattice(k, lam, vmax, iters=600):
    mod, types = classes(k)
    idx = {r: i for i, r in enumerate(types)}
    sub = 3 ** (k - 1)
    lifts = {c: [r for r in types if r % sub == c] for c in range(sub)}
    ch = {r: children(r, k, vmax, 'full') for r in types}
    A = [1.0] * len(types)
    B = [1.0] * len(types)
    rate = 1.0
    for _ in range(iters):
        nA = []
        for r in types:
            tot = 0.0
            for v, c in ch[r]:
                tot += lam ** (-v) * min(B[idx[rr]] for rr in lifts[c])
            nA.append(tot)
        nB = []
        for r in types:
            tot = 0.0
            for v, c in ch[r]:
                if v == 1:
                    tot += min(nA[idx[rr]] for rr in lifts[c])
                else:
                    tot += lam ** (1 - v) * min(B[idx[rr]] for rr in lifts[c])
            nB.append(tot)
        rate = max(max(nA), max(nB))
        A = [x / rate for x in nA]
        B = [x / rate for x in nB]
    return rate

def exponent_lattice(k, vmax):
    lo, hi = 1.0, 2.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if growth_lattice(k, mid, vmax) >= 1.0:
            lo = mid
        else:
            hi = mid
    import math
    return math.log2(lo)

if __name__ == "__main__" and len(sys.argv) > 3 and sys.argv[3] == "lattice":
    for vm in (18, 24, 30, 40):
        for k in range(2, kmax + 1):
            print(f"lattice: vmax = {vm:2d}, classes mod 3^{k} ({len(classes(k)[1]):4d}): "
                  f"exponent {exponent_lattice(k, vm):.4f}")

# ---------------------------------------------------------------------------
# Same lattice, but with a double induction: outer on the index y, inner
# (strong) on the root a.  At index y the claims for any root c < a are
# available, and the v = 1 child is the only child below its parent.
#   F-step (scale 2^y a):    child v may use H(y - v)          weight lam^{-v}
#                            or        F(y - v + 1)            weight lam^{1-v}
#                            (v = 1 uses the inner induction in the F option)
#   H-step (scale 3 2^y a):  child v may use H(y - v + 1)      weight lam^{1-v}
#                            (v = 1 via the inner induction), and for v >= 3
#                            also F(y - v + 2)                 weight lam^{2-v}.
# Each child takes the better of its available options.

def growth_lattice2(k, lam, vmax, iters=600):
    mod, types = classes(k)
    idx = {r: i for i, r in enumerate(types)}
    sub = 3 ** (k - 1)
    lifts = {c: [r for r in types if r % sub == c] for c in range(sub)}
    ch = {r: children(r, k, vmax, 'full') for r in types}
    A = [1.0] * len(types)
    B = [1.0] * len(types)
    rate = 1.0
    for _ in range(iters):
        nA = []
        for r in types:
            tot = 0.0
            for v, c in ch[r]:
                bb = min(B[idx[rr]] for rr in lifts[c])
                aa = min(A[idx[rr]] for rr in lifts[c])
                tot += max(lam ** (-v) * bb, lam ** (1 - v) * aa)
            nA.append(tot)
        nB = []
        for r in types:
            tot = 0.0
            for v, c in ch[r]:
                bb = min(B[idx[rr]] for rr in lifts[c])
                aa = min(A[idx[rr]] for rr in lifts[c])
                opt = lam ** (1 - v) * bb
                if v >= 3:
                    opt = max(opt, lam ** (2 - v) * aa)
                tot += opt
            nB.append(tot)
        rate = max(max(nA), max(nB))
        A = [x / rate for x in nA]
        B = [x / rate for x in nB]
    return rate

def exponent_lattice2(k, vmax):
    lo, hi = 1.0, 2.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if growth_lattice2(k, mid, vmax) >= 1.0:
            lo = mid
        else:
            hi = mid
    import math
    return math.log2(lo)

if __name__ == "__main__" and len(sys.argv) > 3 and sys.argv[3] == "lattice2":
    for k in range(2, kmax + 1):
        print(f"lattice2: vmax = {vmax:2d}, classes mod 3^{k} ({len(classes(k)[1]):4d}): "
              f"exponent {exponent_lattice2(k, vmax):.4f}")
