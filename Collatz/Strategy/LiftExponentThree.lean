import Collatz.Core.Arith

/-!
# Lifting the exponent at `p = 3`, for powers of two

`Strategy.LiftExponent` develops the `2`-adic valuation (`Val2`).  Nothing in the
repository handles the `3`-adic side, and it is needed to generalize
`Strategy.RunLengthUnbounded` from run length `2` to every run length `j ≥ 2`:
that construction requires `3^j ∣ 2^(k+1) − 1`, which holds exactly when
`2·3^(j−1) ∣ k+1`.

This file proves the half that is needed, in a subtraction-free form:

  `2 ^ (2 · 3^j) = 3^(j+1) · c + 1`  for some `c`,

i.e. `3^(j+1)` divides `2^(2·3^j) − 1`.  The induction is the standard one —
cubing lifts the exponent by exactly one — carried out by hand because this
development has no `ring` tactic.
-/

namespace Collatz
namespace LiftExponentThree

/-! ## Two rearrangements, in place of `ring` -/

theorem nine_mul (x : Nat) : 3 * x * (3 * x) = 9 * (x * x) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm x 3 x, ← Nat.mul_assoc]

theorem sq_three (x : Nat) : (3 * x + 1) * (3 * x + 1) = 9 * (x * x) + 6 * x + 1 := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, nine_mul]
  omega

theorem cube_three (x : Nat) :
    (3 * x + 1) * (3 * x + 1) * (3 * x + 1)
      = 27 * (x * x * x) + 27 * (x * x) + 9 * x + 1 := by
  rw [sq_three, Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have h1 : 9 * (x * x) * (3 * x) = 27 * (x * x * x) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm (x * x) 3 x, ← Nat.mul_assoc, ← Nat.mul_assoc]
  have h2 : 6 * x * (3 * x) = 18 * (x * x) := by
    rw [Nat.mul_assoc, Nat.mul_left_comm x 3 x, ← Nat.mul_assoc]
  omega

/-! ## The lift -/

/-- **`3^(j+1)` divides `2^(2·3^j) − 1`**, stated without subtraction.  Cubing
raises the power of three by exactly one, which is the `p = 3` case of lifting
the exponent. -/
theorem two_pow_three_pow : ∀ j : Nat, ∃ c : Nat, 2 ^ (2 * 3 ^ j) = 3 ^ (j + 1) * c + 1 := by
  intro j
  induction j with
  | zero => exact ⟨1, by decide⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨3 * (3 ^ j * 3 ^ j) * (c * c * c) + 3 * 3 ^ j * (c * c) + c, ?_⟩
    have hexp : 2 * 3 ^ (j + 1) = 2 * 3 ^ j + 2 * 3 ^ j + 2 * 3 ^ j := by
      rw [Nat.pow_succ]; omega
    have hcube : (2 : Nat) ^ (2 * 3 ^ (j + 1))
        = 2 ^ (2 * 3 ^ j) * 2 ^ (2 * 3 ^ j) * 2 ^ (2 * 3 ^ j) := by
      rw [hexp, Nat.pow_add, Nat.pow_add]
    have hshift : (3 : Nat) ^ (j + 1) * c = 3 * (3 ^ j * c) := by
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ j) 3, Nat.mul_assoc]
    rw [hcube, hc, hshift, cube_three (3 ^ j * c)]
    -- both sides are now polynomials in `3^j` and `c`
    have e2 : (3 ^ j * c) * (3 ^ j * c) = (3 ^ j * 3 ^ j) * (c * c) :=
      Nat.mul_mul_mul_comm _ _ _ _
    have e3 : (3 ^ j * c) * (3 ^ j * c) * (3 ^ j * c)
        = (3 ^ j * 3 ^ j * 3 ^ j) * (c * c * c) := by
      rw [Nat.mul_mul_mul_comm (3 ^ j) c (3 ^ j) c,
          Nat.mul_mul_mul_comm (3 ^ j * 3 ^ j) (c * c) (3 ^ j) c]
    have hp2 : (3 : Nat) ^ (j + 1 + 1) = 9 * 3 ^ j := by
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    rw [e3, e2, hp2]
    have f2 : ∀ Q : Nat, 3 * (Q * (Q * 9)) = Q * (Q * 27) := by
      intro Q
      rw [Nat.mul_left_comm 3 Q, Nat.mul_left_comm 3 Q]
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, f2]

end LiftExponentThree
end Collatz
