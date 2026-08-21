import Collatz.Strategy.CycleCriterion

/-!
# The accumulator's sharp upper bound

`AffineBound.exists_affine_bounded` bounds the additive correction by `3 ^ j`,
and `AffineBoundSharp.exists_affine_bounded_odd` bounds it by `3 ^ a · 2 ^ j`.
Both are true, both are used, and both are consequences of one inequality that
is *attained*:

`2 ^ a · (C_j(x) + 2 ^ j)  ≤  3 ^ a · 2 ^ j`,

that is, `C + 2 ^ j ≤ 3 ^ a · 2 ^ (j − a)` (`affineC_sharp`).

The mechanism is visible in the induction.  An even step doubles `2 ^ j` and
leaves `C` alone, which can only help; an odd step replaces `C + 2 ^ j` by
`3 C + 2 ^ j + 2 ^ (j+1) = 3 (C + 2 ^ j)` while the right-hand side also gains
exactly a factor of three.  So the odd step is *neutral* for this inequality and
the even step is slack — the bound is an equality precisely when every step is
odd, and the word `A ^ (j−a) B ^ a` attains it in general.

Being attained is what makes it sharp: no better bound of this shape exists.
And it dominates both stored bounds, since `2 ^ (j−a) ≤ 2 ^ j` gives the second
immediately and `3 ^ a · 2 ^ (j−a) ≤ 3 ^ j` gives the first.  At the sizes the
cycle work runs on — `j = 520`, `a = 328` — the improvement over the stored
bound is a factor of about `10 ^ 34`.

What it does *not* do is improve any cycle exclusion, because the cycle bound is
driven by the *lower* bound on `C` together with the gap, not by this side.  It
is recorded here as the sharp form of a fact the development was keeping in two
weaker copies.
-/

namespace Collatz
namespace AccumulatorSharp

open Congruence AffineExact

/-- **The sharp bound.**  Attained by the word that takes every odd step first. -/
theorem affineC_sharp (x : Nat) : ∀ j : Nat,
    2 ^ oddCount x j * (affineC j x + 2 ^ j) ≤ 3 ^ oddCount x j * 2 ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hlast := Density.oddCount_succ_last x j
    rcases Arith.mod_two_eq_zero_or_one (acceleratedOrbit j x) with he | ho
    · -- even step: the correction stands still while the window doubles
      have hcount : oddCount x (j + 1) = oddCount x j := by omega
      rw [hcount, affineC_even he, Arith.two_pow_succ]
      have hstep : 2 ^ oddCount x j * (affineC j x + 2 * 2 ^ j)
          ≤ 2 * (2 ^ oddCount x j * (affineC j x + 2 ^ j)) := by
        have hexp : 2 * (2 ^ oddCount x j * (affineC j x + 2 ^ j))
            = 2 ^ oddCount x j * (2 * affineC j x + 2 * 2 ^ j) := by
          rw [← Nat.mul_left_comm, Nat.mul_add]
        have hmono : 2 ^ oddCount x j * (affineC j x + 2 * 2 ^ j)
            ≤ 2 ^ oddCount x j * (2 * affineC j x + 2 * 2 ^ j) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have hdouble : 2 * (3 ^ oddCount x j * 2 ^ j) = 3 ^ oddCount x j * (2 * 2 ^ j) :=
        Nat.mul_left_comm 2 (3 ^ oddCount x j) (2 ^ j)
      omega
    · -- odd step: both sides gain exactly a factor of three
      have hcount : oddCount x (j + 1) = oddCount x j + 1 := by omega
      rw [hcount, affineC_odd ho, Arith.two_pow_succ, Arith.two_pow_succ,
        Arith.three_pow_succ]
      have hleft : 2 * 2 ^ oddCount x j * (3 * affineC j x + 2 ^ j + 2 * 2 ^ j)
          = 2 * (3 * (2 ^ oddCount x j * (affineC j x + 2 ^ j))) := by
        have h1 : 3 * affineC j x + 2 ^ j + 2 * 2 ^ j = 3 * (affineC j x + 2 ^ j) := by omega
        rw [h1]
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hright : 3 * 3 ^ oddCount x j * (2 * 2 ^ j)
          = 2 * (3 * (3 ^ oddCount x j * 2 ^ j)) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [hleft, hright]
      have := Nat.mul_le_mul_left 3 ih
      omega

/-- The stored bound `C + 2 ^ j ≤ 3 ^ a · 2 ^ j` follows, since `2 ^ a ≥ 1`. -/
theorem affineC_le_three_pow_mul (x j : Nat) :
    affineC j x + 2 ^ j ≤ 3 ^ oddCount x j * 2 ^ j := by
  have hs := affineC_sharp x j
  have hone : 1 * (affineC j x + 2 ^ j) ≤ 2 ^ oddCount x j * (affineC j x + 2 ^ j) :=
    Nat.mul_le_mul_right _ (Arith.one_le_two_pow _)
  omega

/-- The sharp bound in the form that names the shortfall: the correction is
smaller than the trivial bound by the full factor `2 ^ a`. -/
theorem affineC_shortfall (x j : Nat) :
    2 ^ oddCount x j * affineC j x + 2 ^ oddCount x j * 2 ^ j ≤ 3 ^ oddCount x j * 2 ^ j := by
  have hs := affineC_sharp x j
  rw [Nat.mul_add] at hs
  exact hs

end AccumulatorSharp
end Collatz
