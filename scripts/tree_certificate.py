#!/usr/bin/env python3
"""Generate Collatz/Strategy/TreeCertificate.lean: an integer certificate for
the two-type lattice induction of SPEC_treehalf (section 3/4) at ratio
lambda = p/q = 71/50 with K = 4 (parent classes r mod 81, children mod 27).

Everything in the final verification is exact integer / Fraction arithmetic.

Usage:  python3 scripts/tree_certificate.py [--out PATH] [--json]
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction

P, Q = 71, 50           # lambda = P/Q
V = 18                  # clearing exponent (max template valuation)
YBASE = 22              # base cases y <= YBASE; the inductive step starts at y = 23
MOD = 81                # parent class modulus (3^4)
CMOD = 27               # child class modulus (3^3)
NCH = 6                 # children per fertile node


# ---------------------------------------------------------------- classes --
def v0R(r: int) -> int:
    return 2 if r % 3 == 1 else 1


def phaseR(r: int) -> int:
    b = (2 ** v0R(r) * r) % 9
    return 0 if b == 1 else (1 if b == 7 else 2)


def fvalR(r: int, i: int) -> int:
    # Nat subtraction: i + 2 - phase >= 0 always since phase <= 2.
    return v0R(r) + 2 * (i + (i + 2 - phaseR(r)) // 2)


def childRes(r: int, v: int) -> int:
    m = (2 ** v * r) % MOD
    assert m % 3 == 1, (r, v, m)
    return (m - 1) // 3


FERTILE = [r for r in range(MOD) if r % 3 != 0]
assert len(FERTILE) == 54

# Sanity: every fertile parent's children are fertile residues mod 27 and the
# template bound holds.
TMPL = [4, 6, 10, 12, 16, 18]
for r in FERTILE:
    for i in range(NCH):
        v = fvalR(r, i)
        assert 1 <= v <= TMPL[i], (r, i, v)
        c = childRes(r, v)
        assert 0 <= c < CMOD and c % 3 != 0, (r, i, v, c)


# ------------------------------------------------------------- the system --
def amin(tab, c):
    """min over the three lifts r' = c mod 27, r' < 81 (c < 27)."""
    return min(tab[c], tab[c + 27], tab[c + 54])


def rhsF(A, B, r):
    """RHS of the F-inequality for class r, as a list of the 6 max-terms."""
    terms = []
    for i in range(NCH):
        v = fvalR(r, i)
        c = childRes(r, v)
        t1 = Q ** v * P ** (V - v) * amin(B, c)
        t2 = Q ** (v - 1) * P ** (V - v + 1) * amin(A, c)
        terms.append(max(t1, t2))
    return terms


def rhsH(A, B, r):
    terms = []
    for i in range(NCH):
        v = fvalR(r, i)
        c = childRes(r, v)
        t1 = Q ** (v - 1) * P ** (V - v + 1) * amin(B, c)
        t2 = Q ** (v - 2) * P ** (V - v + 2) * amin(A, c) if v >= 3 else 0
        terms.append(max(t1, t2))
    return terms


def apply_map(A, B):
    """The monotone homogeneous map w -> F_lambda(w) (Fractions), i.e. the
    largest tables the inequalities would allow given the current tables."""
    A2 = [Fraction(0)] * MOD
    B2 = [Fraction(0)] * MOD
    for r in FERTILE:
        A2[r] = Fraction(sum(rhsF(A, B, r)), P ** V)
        B2[r] = Fraction(sum(rhsH(A, B, r)), P ** V)
    return A2, B2


def slacks(A, B):
    sF = [sum(rhsF(A, B, r)) - A[r] * P ** V for r in FERTILE]
    sH = [sum(rhsH(A, B, r)) - B[r] * P ** V for r in FERTILE]
    return sF, sH


def check(A, B):
    sF, sH = slacks(A, B)
    return min(sF), min(sH)


# ----------------------------------------------------------- fixed point --
def power_iterate(iters=400):
    A = [Fraction(1) if r % 3 else Fraction(0) for r in range(MOD)]
    B = [Fraction(1) if r % 3 else Fraction(0) for r in range(MOD)]
    rho = None
    for it in range(iters):
        A2, B2 = apply_map(A, B)
        nrm = max(max(A2), max(B2))
        rho = nrm  # growth factor since previous iterate had max 1
        A = [x / nrm for x in A2]
        B = [x / nrm for x in B2]
        # limit denominators to keep Fractions small (still exact arithmetic,
        # only the iterate is perturbed, and the final check is independent).
        A = [x.limit_denominator(10 ** 12) for x in A]
        B = [x.limit_denominator(10 ** 12) for x in B]
    return A, B, rho


def integerize(A, B, scale):
    Ai = [int(x * scale) for x in A]  # floor (all nonnegative)
    Bi = [int(x * scale) for x in B]
    # Decreasing repair: A <- min(A, floor(F(A))).  Terminates at a point
    # A* with A* <= floor(F(A*)) <= F(A*), which is exactly the certificate.
    for _ in range(10_000):
        changed = False
        for r in FERTILE:
            fa = sum(rhsF(Ai, Bi, r)) // P ** V
            fb = sum(rhsH(Ai, Bi, r)) // P ** V
            if fa < Ai[r]:
                Ai[r] = fa
                changed = True
            if fb < Bi[r]:
                Bi[r] = fb
                changed = True
        if not changed:
            break
    return Ai, Bi


def choose_K(Ai, Bi):
    m = max(max(Ai), max(Bi))
    K = 1
    while any(m * P ** y > Q ** y * K for y in range(YBASE + 1)):
        K *= 10
    return K


# ------------------------------------------------------------------ Lean --
def lean_list(tab):
    parts = []
    line = " "
    for x in tab:
        s = f" {x},"
        if len(line) + len(s) > 96:
            parts.append(line)
            line = " "
        line += s
    parts.append(line)
    body = "\n".join(parts).rstrip(",")
    return "[\n" + body + "]"


CERTF_STMT = ("theorem certF : ∀ r, r < 81 → r % 3 ≠ 0 →\n"
              "    A r * 71 ^ 18 ≤ sumRange 6 (fun i =>\n"
              "      max (50 ^ fvalR r i * 71 ^ (18 - fvalR r i) * Bmin (childRes r (fvalR r i)))\n"
              "          (50 ^ (fvalR r i - 1) * 71 ^ (18 - fvalR r i + 1)\n"
              "            * Amin (childRes r (fvalR r i))))")

CERTH_STMT = ("theorem certH : ∀ r, r < 81 → r % 3 ≠ 0 →\n"
              "    B r * 71 ^ 18 ≤ sumRange 6 (fun i =>\n"
              "      max (50 ^ (fvalR r i - 1) * 71 ^ (18 - fvalR r i + 1) * Bmin (childRes r (fvalR r i)))\n"
              "          (if 3 ≤ fvalR r i then\n"
              "            50 ^ (fvalR r i - 2) * 71 ^ (18 - fvalR r i + 2)\n"
              "              * Amin (childRes r (fvalR r i))\n"
              "          else 0))")


def emit_lean(Ai, Bi, K, minF, minH, rho):
    return f'''import Collatz.Strategy.TreeBranching

/-!
# Certificate tables for the exponent-`1/2` tree count

**GENERATED FILE — do not edit by hand.**  Produced by
`scripts/tree_certificate.py`; rerun the script to regenerate.

Parent classes are residues `r` modulo `81` prime to `3` (54 classes); a
child's residue modulo `27` is `childRes r v = ((2 ^ v * r) % 81 - 1) / 3`.
The integer tables `A`, `B` satisfy the `108` inequalities of the two-type
lattice induction at ratio `λ = 71 / 50` with clearing exponent `V = 18`
(`certF`, `certH`), the lift bound `amin_le`, and the base-case bound
`base_bound` with scaling constant `K = {K}`.

Script report: Perron growth factor of the map at `λ = 71/50` ≈ `{float(rho):.5f}`;
minimum slack `RHS − LHS` (in the units of the inequalities, i.e. scaled by `71 ^ 18`)
over the `F`-inequalities
  `{minF}`,
over the `H`-inequalities
  `{minH}`.
-/

namespace Collatz
namespace TreeCertificate

open Collatz.Sum

/-- The `F`-table, indexed by `r < 81` (`0` at `r % 3 = 0`). -/
def Atab : List Nat := {lean_list(Ai)}

/-- The `F`-constant of the class `r mod 81`. -/
def A (r : Nat) : Nat := Atab.getD r 0

/-- The `H`-table, indexed by `r < 81` (`0` at `r % 3 = 0`). -/
def Btab : List Nat := {lean_list(Bi)}

/-- The `H`-constant of the class `r mod 81`. -/
def B (r : Nat) : Nat := Btab.getD r 0

/-- The minimum of `A` over the three lifts of a residue `c < 27` to `r < 81`. -/
def Amin (c : Nat) : Nat := min (A c) (min (A (c + 27)) (A (c + 54)))

/-- The minimum of `B` over the three lifts of a residue `c < 27` to `r < 81`. -/
def Bmin (c : Nat) : Nat := min (B c) (min (B (c + 27)) (B (c + 54)))

/-- `TreeCount.v0` as a function of the residue. -/
def v0R (r : Nat) : Nat := if r % 3 = 1 then 2 else 1

/-- `TreeBranching.phase` as a function of the residue mod `9`. -/
def phaseR (r : Nat) : Nat :=
  let b := 2 ^ v0R r * r % 9
  if b = 1 then 0 else if b = 7 then 1 else 2

/-- `TreeBranching.fval` as a function of the residue: the `i`-th fertile valuation. -/
def fvalR (r i : Nat) : Nat := v0R r + 2 * (i + (i + 2 - phaseR r) / 2)

/-- The residue mod `27` of `child a v` when `a ≡ r (mod 81)`. -/
def childRes (r v : Nat) : Nat := ((2 ^ v * r) % 81 - 1) / 3

/-- The scaling constant of the claims `A r * 71 ^ y ≤ 50 ^ y * K * S a (2 ^ y * a)`. -/
def K : Nat := {K}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The `F`-step inequalities, one per fertile class. -/
{CERTF_STMT} := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The `H`-step inequalities, one per fertile class. -/
{CERTH_STMT} := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A class's own constant dominates the minimum over the lifts of its child residue. -/
theorem amin_le : ∀ c, c < 81 → c % 3 ≠ 0 →
    Amin (c % 27) ≤ A c ∧ Bmin (c % 27) ≤ B c := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The base case `y ≤ 22`: the claims follow from `S ≥ 1` alone.  (The inductive
step starts at `y = 23`, where every child bound has slack `2 ^ (y − v) ≥ 32 ≥ 18`.) -/
theorem base_bound : ∀ r, r < 81 → ∀ y, y ≤ 22 →
    A r * 71 ^ y ≤ 50 ^ y * K ∧ B r * 71 ^ y ≤ 50 ^ y * K := by
  decide

end TreeCertificate
end Collatz
'''


# ---------------------------------------------------------------- main ---
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="Collatz/Strategy/TreeCertificate.lean")
    ap.add_argument("--scale", type=int, default=10 ** 6)
    ap.add_argument("--iters", type=int, default=300)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    A, B, rho = power_iterate(args.iters)
    if rho <= 1:
        report = {"feasible": False, "lambda": f"{P}/{Q}", "rho": float(rho)}
        print(json.dumps(report, indent=2))
        sys.exit(1)

    Ai, Bi = integerize(A, B, args.scale)
    feasible = all(Ai[r] > 0 and Bi[r] > 0 for r in FERTILE)

    # Exact re-verification with Python integers only.
    minF, minH = check(Ai, Bi)
    assert minF >= 0 and minH >= 0, (minF, minH)
    for c in FERTILE:
        assert amin(Ai, c % 27) <= Ai[c] and amin(Bi, c % 27) <= Bi[c]
    K = choose_K(Ai, Bi)
    for r in range(MOD):
        for y in range(YBASE + 1):
            assert Ai[r] * P ** y <= Q ** y * K and Bi[r] * P ** y <= Q ** y * K

    lean = emit_lean(Ai, Bi, K, minF, minH, rho)
    with open(args.out, "w") as f:
        f.write(lean)

    report = {
        "feasible": feasible,
        "lambda": f"{P}/{Q}",
        "rho_float": float(rho),
        "K": K,
        "min_slack_F": minF,
        "min_slack_H": minH,
        "min_slack_F_rel": float(Fraction(minF, P ** V) / max(Ai)),
        "min_slack_H_rel": float(Fraction(minH, P ** V) / max(Bi)),
        "maxA": max(Ai), "minA": min(Ai[r] for r in FERTILE),
        "maxB": max(Bi), "minB": min(Bi[r] for r in FERTILE),
        "out": args.out,
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
