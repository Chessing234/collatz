import Collatz.Strategy.CycleProduct

/-!
# The additive correction, exactly

`AffineBound` knows that `2 ^ j · T^j(x) = 3 ^ a · x + b` for *some* `b` with a
crude bound.  This file computes `b` outright, by the recursion it actually
satisfies, and uses it to convert never-dropping into a purely arithmetic
condition with no orbit quantifier left on the right.

## The recursion

Writing `C j x` for the correction after `j` steps:

* an **odd** step sends `C ↦ 3C + 2 ^ j`;
* an **even** step leaves `C` unchanged.

So the whole additive content of the `+1` in `3n + 1` is a single accumulator
that is fed only by odd steps (`affineC_odd`, `affineC_even`), and

`2 ^ j · T^j(x) = 3 ^ (oddCount x j) · x + affineC j x`   (`affine_exact`).

Verified against real orbits on 120 000 exact instances before formalising.

## Never-dropping becomes arithmetic

`T^j(x) ≥ m` is, after multiplying by `2 ^ j`, exactly
`2 ^ j · m ≤ 3 ^ a · m + C`.  So

**`m` never drops  ↔  `∀ j, 2 ^ j · m ≤ 3 ^ (oddCount m j) · m + affineC j m`**

(`neverDrops_iff_affine`).  The dynamical hypothesis is gone; what remains is a
family of inequalities among `2 ^ j`, `3 ^ a` and one explicit integer.

## What the correction is worth

`affineC` is minimised, for a given odd-step count, by taking all the odd steps
first, which gives `affineC j x + 2 ^ a ≥ 3 ^ a` (`three_pow_le_affineC`).
And `CycleProduct.neverDrops_product_bound` is exactly an *upper* bound on the
same quantity.  The two together sandwich `C`:

`(2 ^ j − 3 ^ a) · m  ≤  C  ≤  m · ((3 + 1/m) ^ a − 3 ^ a)`.

**Honest finding: the sandwich carries no new information.** The two sides are
compatible precisely when `2 ^ j ≤ (3 + 1/m) ^ a`, which is the product bound
restated.  So "find two inequalities on the same intermediate quantity" is
already exhausted here — recorded so the direction is not re-attempted.

## A correction about the threshold `a = 3m/2`

That threshold is an artifact of the *linearisation* `pow_succ_le`, which needs
`2a ≤ 3m`.  The underlying bound `2 ^ k · m ^ a ≤ (3m+1) ^ a` carries **no side
condition at all** and stays active well past it — checked at `m = 101`, where at
`a = 152 > 3m/2 = 151.5` it still forces `a/k ≥ 0.6307`.  Any simplified form
such as `2 ^ k ≤ 2 · 3 ^ a` introduces a threshold of its own (there, `a ≲ 2.08m`),
but the threshold belongs to the simplification, not to the mathematics.  There
is no second regime needing a separate theorem.
-/

namespace Collatz
namespace AffineExact

open Reach Congruence

/-! ## The accumulator -/

/-- The additive correction after `j` steps, fed only by odd steps. -/
def affineC : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, x =>
      if acceleratedOrbit j x % 2 = 1 then 3 * affineC j x + 2 ^ j else affineC j x

@[simp] theorem affineC_zero (x : Nat) : affineC 0 x = 0 := rfl

theorem affineC_odd {j x : Nat} (h : acceleratedOrbit j x % 2 = 1) :
    affineC (j + 1) x = 3 * affineC j x + 2 ^ j := by
  rw [affineC, if_pos h]

theorem affineC_even {j x : Nat} (h : acceleratedOrbit j x % 2 = 0) :
    affineC (j + 1) x = affineC j x := by
  rw [affineC, if_neg (by omega)]

/-! ## The exact affine identity -/

/-- **The affine identity with the correction computed.** -/
theorem affine_exact (x : Nat) : ∀ j : Nat,
    2 ^ j * acceleratedOrbit j x = 3 ^ oddCount x j * x + affineC j x := by
  intro j
  induction j with
  | zero => simp [acceleratedOrbit]
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    have hstep : acceleratedOrbit (j + 1) x = acceleratedStep (acceleratedOrbit j x) :=
      acceleratedOrbit_succ_step j x
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hcount : oddCount x (j + 1) = oddCount x j := by omega
      have hval : acceleratedStep (acceleratedOrbit j x) = acceleratedOrbit j x / 2 := by
        rw [acceleratedStep, if_pos he]
      have hhalf : 2 * (acceleratedOrbit j x / 2) = acceleratedOrbit j x := by omega
      have hkey : 2 ^ (j + 1) * (acceleratedOrbit j x / 2)
          = 2 ^ j * acceleratedOrbit j x := by
        rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm, hhalf]
      rw [hstep, hval, hcount, affineC_even he, hkey]
      exact ih
    · have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      have hval : acceleratedStep (acceleratedOrbit j x)
          = (3 * acceleratedOrbit j x + 1) / 2 := by
        rw [acceleratedStep, if_neg (by omega)]
      have hpar : 2 * ((3 * acceleratedOrbit j x + 1) / 2)
          = 3 * acceleratedOrbit j x + 1 := by omega
      have hkey : 2 ^ (j + 1) * ((3 * acceleratedOrbit j x + 1) / 2)
          = 2 ^ j * (3 * acceleratedOrbit j x + 1) := by
        rw [Arith.two_pow_succ, Nat.mul_assoc, Nat.mul_left_comm, hpar]
      rw [hstep, hval, hcount, affineC_odd ho, hkey, Nat.pow_succ]
      have hexp : 2 ^ j * (3 * acceleratedOrbit j x + 1)
          = 3 * (2 ^ j * acceleratedOrbit j x) + 2 ^ j := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]
      rw [hexp, ih]
      have hr : 3 ^ oddCount x j * 3 * x = 3 * (3 ^ oddCount x j * x) := by
        rw [Nat.mul_comm (3 ^ oddCount x j) 3, Nat.mul_assoc]
      omega

/-! ## Never-dropping, arithmetised -/

/-- **Never-dropping is an arithmetic condition.**  No orbit quantifier remains
on the right: only `2 ^ j`, `3 ^ a` and the explicit accumulator. -/
theorem neverDrops_iff_affine {m : Nat} (hm : 0 < m) :
    (∀ j : Nat, m ≤ acceleratedOrbit j m)
      ↔ (∀ j : Nat, 2 ^ j * m ≤ 3 ^ oddCount m j * m + affineC j m) := by
  constructor
  · intro h j
    have hexact := affine_exact m j
    have hmono : 2 ^ j * m ≤ 2 ^ j * acceleratedOrbit j m :=
      Nat.mul_le_mul_left _ (h j)
    omega
  · intro h j
    have hexact := affine_exact m j
    have hle := h j
    have hpos : 0 < (2:Nat) ^ j := Arith.two_pow_pos j
    have hmono : 2 ^ j * m ≤ 2 ^ j * acceleratedOrbit j m := by omega
    exact Nat.le_of_mul_le_mul_left hmono hpos

/-- The odd-step count never exceeds the window length. -/
theorem oddCount_le_self (x : Nat) : ∀ j : Nat, oddCount x j ≤ j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl 0
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    have hpar := Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x)
    omega

/-! ## How large the correction is -/

/-- The correction is at least `3 ^ a − 2 ^ a`, stated without subtraction.  The
minimum is attained by taking every odd step first. -/
theorem three_pow_le_affineC (x : Nat) : ∀ j : Nat,
    3 ^ oddCount x j ≤ affineC j x + 2 ^ oddCount x j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hcount, affineC_even he]
      exact ih
    · have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      rw [hcount, affineC_odd ho, Nat.pow_succ, Nat.pow_succ]
      have hmul : 3 ^ oddCount x j * 3
          ≤ (affineC j x + 2 ^ oddCount x j) * 3 := Nat.mul_le_mul_right _ ih
      have hexp : (affineC j x + 2 ^ oddCount x j) * 3
          = 3 * affineC j x + 2 ^ oddCount x j * 3 := by
        rw [Nat.add_mul, Nat.mul_comm (affineC j x) 3]
      have hgrow : 2 ^ oddCount x j * 2 ≤ 2 ^ oddCount x j * 3 :=
        Nat.mul_le_mul_left _ (by omega)
      have hpow : (2:Nat) ^ oddCount x j ≤ 2 ^ j :=
        Arith.two_pow_le_two_pow (oddCount_le_self x j)
      omega

end AffineExact
end Collatz
