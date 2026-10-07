import Collatz.Exploration.FloorProductError

/-! Integer Bernoulli comparison of the two floor-error budgets.
The underlying inequality is classical; no priority claim is made. -/
namespace Collatz.Exploration.FloorBudgetComparison
open FloorAffineError FloorProductError

/-- Cleared-denominator Bernoulli inequality for neighboring positive bases. -/
theorem bernoulli_neighbors (v k : Nat) :
    (v+1)^(k+1) ≤ (v+1)*v^k+k*(v+1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := Nat.mul_le_mul_left v ih
    have h2 := Nat.mul_le_mul_left (k*(v+1)^k) (show v ≤ v+1 by omega)
    simp only [Nat.pow_succ,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_left_comm,Nat.mul_comm] at h1 h2 ⊢
    omega

/-- The multiplicative offset ratio is no worse than the linear ratio when k<w. -/
theorem ratio_comparison (b k : Nat) :
    (weight b-k)*weight b^k ≤ weight b*base b^k := by
  have hh := bernoulli_neighbors (base b) k
  have hw : base b+1=weight b := by unfold base weight; rfl
  rw [hw,Nat.pow_succ] at hh
  rw [Nat.sub_mul]
  simp only [Nat.mul_comm] at hh ⊢
  omega

/-- Compare the paid-offset coefficients when the linear denominator is positive. -/
theorem paid_ratio_comparison {b k : Nat} (hk : k ≤ weight b) :
    (weight b-k)*(weight b^k-base b^k) ≤ k*base b^k := by
  have hr := ratio_comparison b k
  have he := congrArg (fun z => z*base b^k) (Nat.sub_add_cancel hk)
  rw [Nat.add_mul] at he
  rw [Nat.mul_sub]
  omega

end Collatz.Exploration.FloorBudgetComparison
