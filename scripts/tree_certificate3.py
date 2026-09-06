#!/usr/bin/env python3
"""Generate Collatz/Strategy/TreeCertificate3.lean: the integer certificate for
the ABSOLUTE-BOUND double induction (Strategy/TreeSevenTenths) at parent classes
modulo 729, children modulo 243, ratio lambda = P/Q = 13/8 (so lambda^10 >= 2^7,
exponent 7/10), clearing exponent V = 18.

Claims (for a root a of class r):  F: A r * 8^y <= 5^y K S(a, 2^y a),
                                   H: B r * 8^y <= 5^y K S(a, 3 2^y a).
F-step (bound 2^y a): child at valuation v uses H(y-v) [weight lam^-v] or
F(y-v+1) [lam^(1-v)].  H-step (bound 3 2^y a): H(y-v+1) [lam^(1-v)] or
F(y-v+3) [lam^(3-v)] -- the latter is 'advanced' for v <= 2 and is available
because the induction runs on the absolute bound.  Cleared inequalities:
  F:  A r * 8^18      <= sum_i max(5^v 8^(18-v) Bmin, 5^(v-1) 8^(19-v) Amin)
  H:  B r * 8^18 * 25 <= sum_i max(5^(v+1) 8^(19-v) Bmin, 5^(v-1) 8^(21-v) Amin)
All final checks are exact integer arithmetic.
Usage: python3 scripts/tree_certificate3.py [--out PATH]
"""
import argparse, json, sys
from fractions import Fraction

P, Q = 13, 8
V = 18
YBASE = 22
MOD, CMOD = 729, 243
NCH = 6

def v0R(r): return 2 if r % 3 == 1 else 1
def phaseR(r):
    b = (2 ** v0R(r) * r) % 9
    return 0 if b == 1 else (1 if b == 7 else 2)
def fvalR(r, i): return v0R(r) + 2 * (i + (i + 2 - phaseR(r)) // 2)
def childRes(r, v):
    m = (2 ** v * r) % MOD
    assert m % 3 == 1
    return (m - 1) // 3

FERTILE = [r for r in range(MOD) if r % 3 != 0]
TMPL = [4, 6, 10, 12, 16, 18]
for r in FERTILE:
    for i in range(NCH):
        v = fvalR(r, i); assert 1 <= v <= TMPL[i]
        c = childRes(r, v); assert 0 <= c < CMOD and c % 3 != 0

def amin(tab, c): return min(tab[c], tab[c + CMOD], tab[c + 2 * CMOD])

def rhsF(A, B, r):
    out = []
    for i in range(NCH):
        v = fvalR(r, i); c = childRes(r, v)
        out.append(max(Q ** v * P ** (V - v) * amin(B, c), Q ** (v - 1) * P ** (V - v + 1) * amin(A, c)))
    return out

def rhsH(A, B, r):
    out = []
    for i in range(NCH):
        v = fvalR(r, i); c = childRes(r, v)
        out.append(max(Q ** (v + 1) * P ** (V - v + 1) * amin(B, c), Q ** (v - 1) * P ** (V - v + 3) * amin(A, c)))
    return out

def apply_map(A, B):
    A2 = [Fraction(0)] * MOD; B2 = [Fraction(0)] * MOD
    for r in FERTILE:
        A2[r] = Fraction(sum(rhsF(A, B, r)), P ** V)
        B2[r] = Fraction(sum(rhsH(A, B, r)), P ** V * Q ** 2)
    return A2, B2

def check(A, B):
    sF = [sum(rhsF(A, B, r)) - A[r] * P ** V for r in FERTILE]
    sH = [sum(rhsH(A, B, r)) - B[r] * P ** V * Q ** 2 for r in FERTILE]
    return min(sF), min(sH)

def power_iterate(iters):
    A = [Fraction(1) if r % 3 else Fraction(0) for r in range(MOD)]
    B = list(A)
    import math
    logs = []
    for it in range(iters):
        A2, B2 = apply_map(A, B)
        tot = sum(A2) + sum(B2); logs.append(math.log(float(tot) / float(sum(A) + sum(B))))
        A = [(x / tot).limit_denominator(10 ** 12) for x in A2]
        B = [(x / tot).limit_denominator(10 ** 12) for x in B2]
    return A, B, math.exp(sum(logs[-40:]) / 40)

def integerize(A, B, scale):
    Ai = [int(x * scale) for x in A]; Bi = [int(x * scale) for x in B]
    for _ in range(100000):
        changed = False
        for r in FERTILE:
            fa = sum(rhsF(Ai, Bi, r)) // P ** V
            fb = sum(rhsH(Ai, Bi, r)) // (P ** V * Q ** 2)
            if fa < Ai[r]: Ai[r] = fa; changed = True
            if fb < Bi[r]: Bi[r] = fb; changed = True
        if not changed: break
    return Ai, Bi

def choose_K(Ai, Bi):
    m = max(max(Ai), max(Bi)); K = 1
    while any(m * P ** y > Q ** y * K for y in range(YBASE + 1)): K *= 10
    return K

def lean_list(tab):
    parts, line = [], " "
    for x in tab:
        s = f" {x},"
        if len(line) + len(s) > 96: parts.append(line); line = " "
        line += s
    parts.append(line)
    return "[\n" + "\n".join(parts).rstrip(",") + "]"

def emit(Ai, Bi, K, minF, minH, rho):
    return f'''import Collatz.Strategy.TreeBranching

/-!
# Certificate tables for the exponent-`7/10` tree count

**GENERATED FILE — do not edit by hand.**  Produced by
`scripts/tree_certificate3.py`; rerun the script to regenerate.

Parent classes are residues `r` modulo `729` prime to `3` (486 classes); a
child's residue modulo `243` is `childRes r v = ((2 ^ v * r) % 729 - 1) / 3`.
The tables `A`, `B` satisfy the `972` inequalities of the absolute-bound
double induction at ratio `λ = 13 / 8` (`certF`, `certH`), the lift bound
`amin_le`, and the base-case bound `base_bound` with `K = {K}`.

Script report: growth factor of the map at `λ = 13/8` ≈ `{rho:.5f}`; minimum
slack `RHS − LHS` over the `F`-inequalities `{minF}`, over the `H`-inequalities
`{minH}` (units: scaled by `13 ^ 18`, resp. `13 ^ 18 · 64`).
-/

namespace Collatz
namespace TreeCertificate3

open Collatz.Sum

/-- The `F`-table, indexed by `r < 729` (`0` at `r % 3 = 0`). -/
def Atab : List Nat := {lean_list(Ai)}

def A (r : Nat) : Nat := Atab.getD r 0

/-- The `H`-table, indexed by `r < 729` (`0` at `r % 3 = 0`). -/
def Btab : List Nat := {lean_list(Bi)}

def B (r : Nat) : Nat := Btab.getD r 0

/-- The minimum of `A` over the three lifts of `c < 243` to `r < 729`. -/
def Amin (c : Nat) : Nat := min (A c) (min (A (c + 243)) (A (c + 486)))

def Bmin (c : Nat) : Nat := min (B c) (min (B (c + 243)) (B (c + 486)))

def v0R (r : Nat) : Nat := if r % 3 = 1 then 2 else 1

def phaseR (r : Nat) : Nat :=
  let b := 2 ^ v0R r * r % 9
  if b = 1 then 0 else if b = 7 then 1 else 2

/-- `TreeBranching.fval` as a function of the residue. -/
def fvalR (r i : Nat) : Nat := v0R r + 2 * (i + (i + 2 - phaseR r) / 2)

/-- The residue mod `243` of `child a v` when `a ≡ r (mod 729)`. -/
def childRes (r v : Nat) : Nat := ((2 ^ v * r) % 729 - 1) / 3

def K : Nat := {K}

set_option maxRecDepth 400000 in
set_option maxHeartbeats 400000000 in
/-- The `F`-step inequalities, one per fertile class. -/
theorem certF : ∀ r, r < 729 → r % 3 ≠ 0 →
    A r * 13 ^ 18 ≤ sumRange 6 (fun i =>
      max (8 ^ fvalR r i * 13 ^ (18 - fvalR r i) * Bmin (childRes r (fvalR r i)))
          (8 ^ (fvalR r i - 1) * 13 ^ (18 - fvalR r i + 1)
            * Amin (childRes r (fvalR r i)))) := by
  decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 400000000 in
/-- The `H`-step inequalities, one per fertile class. -/
theorem certH : ∀ r, r < 729 → r % 3 ≠ 0 →
    B r * 13 ^ 18 * 64 ≤ sumRange 6 (fun i =>
      max (8 ^ (fvalR r i + 1) * 13 ^ (18 - fvalR r i + 1) * Bmin (childRes r (fvalR r i)))
          (8 ^ (fvalR r i - 1) * 13 ^ (18 - fvalR r i + 3)
            * Amin (childRes r (fvalR r i)))) := by
  decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 400000000 in
/-- A class's own constant dominates the minimum over the lifts of its child residue. -/
theorem amin_le : ∀ c, c < 729 → c % 3 ≠ 0 →
    Amin (c % 243) ≤ A c ∧ Bmin (c % 243) ≤ B c := by
  decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 400000000 in
/-- The base case `y ≤ 22`. -/
theorem base_bound : ∀ r, r < 729 → ∀ y, y ≤ 22 →
    A r * 13 ^ y ≤ 8 ^ y * K ∧ B r * 13 ^ y ≤ 8 ^ y * K := by
  decide

end TreeCertificate3
end Collatz
'''

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="Collatz/Strategy/TreeCertificate3.lean")
    ap.add_argument("--scale", type=int, default=10 ** 6)
    ap.add_argument("--iters", type=int, default=300)
    args = ap.parse_args()
    A, B, rho = power_iterate(args.iters)
    if rho <= 1:
        print(json.dumps({"feasible": False, "rho": rho})); sys.exit(1)
    Ai, Bi = integerize(A, B, args.scale)
    assert all(Ai[r] > 0 and Bi[r] > 0 for r in FERTILE)
    minF, minH = check(Ai, Bi); assert minF >= 0 and minH >= 0
    for c in FERTILE:
        assert amin(Ai, c % CMOD) <= Ai[c] and amin(Bi, c % CMOD) <= Bi[c]
    K = choose_K(Ai, Bi)
    for r in range(MOD):
        for y in range(YBASE + 1):
            assert Ai[r] * P ** y <= Q ** y * K and Bi[r] * P ** y <= Q ** y * K
    with open(args.out, "w") as f:
        f.write(emit(Ai, Bi, K, minF, minH, rho))
    print(json.dumps({"feasible": True, "rho": rho, "K": K, "minF_rel": float(Fraction(minF, P ** V) / max(Ai)),
                      "minH_rel": float(Fraction(minH, P ** V * Q ** 2) / max(Bi)), "maxA": max(Ai), "maxB": max(Bi)}, indent=1))

if __name__ == "__main__":
    main()
