#!/usr/bin/env python3
"""The tau-orbit decomposition of an inverse-closed set, and why it does not
reduce G8.

tau x = 4x + 1 preserves the Syracuse successor (Strategy/BackwardMixing.
child_succ), so any inverse-closed set is a disjoint union of tau-orbits whose
seeds are its members with x != 5 (mod 8).  With tau_class_eq_iff (tau is a
3^k-cycle mod 3^k) the class counts obey the exact identity

    N_r(X) = sum_{i >= 0} Sd_{tau^(-i) r}(X_i),   X_i = (X + 1/3)/4^i - 1/3,

Sd_c = the seeds in class c.  This checks the identity on a real subtree and
then measures the orbit length L(s) = floor(log_4((3X+1)/(3s+1))) + 1, whose
equidistribution mod 9 is what an averaging argument would need.  It is not
equidistributed: L is concentrated on 1 and 2, because a tau step costs a
factor 4 in size while the tree's mass sits at the top of the range.  So the
identity re-expresses the imbalance instead of averaging it away."""
import math
from collections import Counter

def subtree(a, X):
    out, stack = [], [a]
    while stack:
        n = stack.pop()
        v = 1 if n % 3 == 2 else 2
        while True:
            c = (2 ** v * n - 1) // 3
            if c > X: break
            if c != n:
                out.append(c)
                if c % 3:                 # only fertile nodes have children
                    stack.append(c)
            v += 2
    return out

def tau(c): return 4 * c + 1

a, Y = 1234567, 10 ** 4
X = a * Y
S = subtree(a, X)
Sset = set(S)
m = 9
# direct class counts (fertile members only, as Equi is about those)
direct = Counter(n % m for n in S)

# tau-orbit decomposition: seeds are members whose tau-predecessor is not in S
seeds = [n for n in S if (n - 1) % 4 != 0 or (n - 1) // 4 not in Sset]
print(f"members {len(S)}, seeds {len(seeds)}, ratio {len(seeds)/len(S):.4f}")

# rebuild counts from the seeds
rebuilt = Counter()
Ls = []
for s in seeds:
    L, c = 0, s
    while c <= X:
        rebuilt[c % m] += 1
        c = tau(c); L += 1
    Ls.append((s % m, L))
print("decomposition exact:", direct == rebuilt)

# the reduction: L(s) = floor(log_4((3X+1)/(3s+1))) + 1
Lform = [math.floor(math.log((3*X+1)/(3*s+1), 4)) + 1 for s in seeds]
print("L closed form matches:", all(a1 == b1 for a1, (_, b1) in zip(Lform, Ls)))

# is L mod 9 equidistributed, within each class mod 9?
print(f"\n{'seed class':>10} {'seeds':>7}  L mod 9 histogram (expect flat)")
for c in range(m):
    hs = [L for (r, L) in Ls if r == c]
    if not hs: continue
    h = Counter(L % 9 for L in hs)
    tot = len(hs)
    print(f"{c:>10} {tot:>7}  " + " ".join(f"{h.get(u,0)/tot:.3f}" for u in range(9)))
