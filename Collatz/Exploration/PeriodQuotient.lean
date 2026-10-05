import Collatz.Exploration.AffineRay

/-!
# Executable quotient for a ternary exponent period

The period power exceeds one by an exact multiple of the ternary modulus.
The quotient is computed by natural division, and the earlier exact lifting
identity proves there is no truncation. This bridges existential lifting
coefficients and an executable inverse-family recurrence.
-/
namespace Collatz.Exploration.PeriodQuotient

open ExponentSearch ThreePowerLift

/-- Coefficient of the exact period power minus one. -/
def periodQuotient (a : Nat) : Nat := (2^(periodLength a)-1)/3^a

/-- The quotient reconstructs the period power at every exponent, including
zero, whose modulus is one and period length is one. -/
theorem periodQuotient_exact (a : Nat) :
    3^a*periodQuotient a+1 = 2^(periodLength a) := by
  cases a with
  | zero => decide
  | succ j =>
    obtain ⟨c, _, hc, _⟩ := exact_lift_positive j
    have hp : periodLength (j+1) = 2*3^j := by simp [periodLength]
    unfold periodQuotient
    rw [hp, hc, Nat.add_sub_cancel,
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < (3:Nat)))]

/-- The exact coefficient is positive, so transporting a positive index will
strictly increase it. -/
theorem periodQuotient_positive (a : Nat) : 0 < periodQuotient a := by
  cases a with
  | zero => decide
  | succ j =>
    obtain ⟨c, hcpos, hc, _⟩ := exact_lift_positive j
    have hp : periodLength (j+1) = 2*3^j := by simp [periodLength]
    unfold periodQuotient
    rw [hp, hc, Nat.add_sub_cancel,
      Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < (3:Nat)))]
    exact hcpos

/-- A nontrivial multiplier for all rays, even at the unit modulus. -/
theorem period_factor_gt_one (a : Nat) : 1 < 3^a*periodQuotient a+1 := by
  have hm : 0 < 3^a*periodQuotient a := Nat.mul_pos (Nat.pow_pos (by decide : 0 < (3:Nat)))
    (periodQuotient_positive a)
  omega

end Collatz.Exploration.PeriodQuotient
