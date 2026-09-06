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

# ---------------------------------------------------------------------------
# Multi-type lattice: claim types (j, y) for scales 3^j 2^y a, j = 0..J, with
# the double induction (outer on y, inner on the root).  From type j < J a
# child at valuation v goes EXACTLY to type (j+1, y - v) (retarded, since
# 3^j 2^y a = 3^j 2^(y-v) (3c+1) >= 3^(j+1) 2^(y-v) c); from the top type J
# it goes to (J, y - v + 1) at a loss of 3/2 (index y when v = 1: the child
# is below its parent, inner induction).  Either way each child may also use
# any type (j', y') with 3^j' 2^y' c <= the available bound; we take the best
# of the exact option and, for the top type, the rounded one.

def growth_multi(k, lam, vmax, J, iters=800):
    import math
    mod, types = classes(k)
    idx = {r: i for i, r in enumerate(types)}
    sub = 3 ** (k - 1)
    lifts = {c: [r for r in types if r % sub == c] for c in range(sub)}
    ch = {r: children(r, k, vmax, 'full') for r in types}
    n = len(types)
    W = [[1.0] * n for _ in range(J + 1)]      # W[j][class]
    rate = 1.0
    for _ in range(iters):
        nW = [[0.0] * n for _ in range(J + 1)]
        for j in range(J + 1):
            for r in types:
                tot = 0.0
                for v, c in ch[r]:
                    if j < J:
                        # exact: type (j+1, y - v), weight lam^{-v}
                        tot += lam ** (-v) * min(W[j + 1][idx[rr]] for rr in lifts[c])
                    else:
                        # top type: (J, y - v + 1), weight lam^{1-v}
                        tot += lam ** (1 - v) * min(W[J][idx[rr]] for rr in lifts[c])
                nW[j][idx[r]] = tot
        rate = max(max(row) for row in nW)
        W = [[x / rate for x in row] for row in nW]
    return rate

def exponent_multi(k, vmax, J):
    import math
    lo, hi = 1.0, 2.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if growth_multi(k, mid, vmax, J) >= 1.0:
            lo = mid
        else:
            hi = mid
    return math.log2(lo)

if __name__ == "__main__" and len(sys.argv) > 3 and sys.argv[3] == "multi":
    for k in (4, 5):
        for J in (0, 1, 2, 3, 4, 6, 8):
            print(f"multi: classes mod 3^{k}, J = {J} ({(J+1)*len(classes(k)[1]):5d} constants): "
                  f"exponent {exponent_multi(k, vmax, J):.4f}")

# ---------------------------------------------------------------------------
# Multi-type lattice with induction on the ABSOLUTE bound 3^j 2^y a: from
# type j a child at valuation v has true bound 3^(j+1) 2^(y-v) c and may use
# ANY type j' <= J at index y' = y - v + floor((j+1-j') log2 3) (so that
# 3^j' 2^y' <= 3^(j+1) 2^(y-v)); every such bound is below the parent's, so
# the claim is available by strong induction on the bound.  Each child takes
# the best option.

def growth_abs(k, lam, vmax, J, iters=800):
    import math
    mod, types = classes(k)
    idx = {r: i for i, r in enumerate(types)}
    sub = 3 ** (k - 1)
    lifts = {c: [r for r in types if r % sub == c] for c in range(sub)}
    ch = {r: children(r, k, vmax, 'full') for r in types}
    n = len(types)
    L3 = math.log2(3)
    shifts = {}
    for j in range(J + 1):
        for jp in range(0, min(J, j + 1) + 1):
            shifts[(j, jp)] = math.floor((j + 1 - jp) * L3 + 1e-12)
    W = [[1.0] * n for _ in range(J + 1)]
    rate = 1.0
    for _ in range(iters):
        nW = [[0.0] * n for _ in range(J + 1)]
        for j in range(J + 1):
            for r in types:
                tot = 0.0
                for v, c in ch[r]:
                    best = 0.0
                    for jp in range(0, min(J, j + 1) + 1):
                        e = shifts[(j, jp)]
                        val = lam ** (e - v) * min(W[jp][idx[rr]] for rr in lifts[c])
                        if val > best:
                            best = val
                    tot += best
                nW[j][idx[r]] = tot
        rate = max(max(row) for row in nW)
        W = [[x / rate for x in row] for row in nW]
    return rate

def exponent_abs(k, vmax, J):
    import math
    lo, hi = 1.0, 2.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if growth_abs(k, mid, vmax, J) >= 1.0:
            lo = mid
        else:
            hi = mid
    return math.log2(lo)

if __name__ == "__main__" and len(sys.argv) > 3 and sys.argv[3] == "abs":
    for k in (3, 4, 5):
        for J in (0, 1, 2, 3, 5, 8):
            print(f"abs: classes mod 3^{k}, J = {J} ({(J+1)*len(classes(k)[1]):5d} constants): "
                  f"exponent {exponent_abs(k, vmax, J):.4f}")
