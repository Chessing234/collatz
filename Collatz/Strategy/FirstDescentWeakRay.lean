import Collatz.Strategy.FirstDescentClassComplete
import Collatz.Strategy.FirstDescentContraction

/-!
# An unbounded family of weak first descents

The checked input 4591 extends to the complete dyadic ray `2^65*m+4591`.
Every member first descends at time 65. Its exact affine endpoint is
`3^41*m+4541`, and every member loses less than two percent of its size.
This obstructs a strong fixed contraction at the first checkpoint even
above an arbitrary starting-value threshold.
-/

namespace Collatz.FirstDescentClass

set_option maxRecDepth 20000 in
/-- Complete-class certificate for the weak-drop ray. -/
theorem weak_ray_certificate : classCertificateB 65 4591 = true := by decide

set_option maxRecDepth 20000 in
/-- Exact number of odd steps in the weak-drop base prefix. -/
theorem weak_ray_odd_count : oddCount 4591 65 = 41 := by decide

/-- Every member, including arbitrarily large ones, first descends at the same time. -/
theorem weak_ray_stoppingTime (m : Nat) : stoppingTime (2 ^ 65 * m + 4591) 65 :=
  stoppingTime_of_classCertificate weak_ray_certificate m

/-- Exact endpoint formula for every member of the weak-drop ray. -/
theorem weak_ray_endpoint (m : Nat) :
    acceleratedOrbit 65 (2 ^ 65 * m + 4591) = 3 ^ 41 * m + 4541 := by
  rw [Congruence.accOrbit_pow_two_mul_add, weak_ray_odd_count,
    FirstDescentResidue.landing_4591]

/-- Every endpoint on the ray is strictly below its own starting value. -/
theorem weak_ray_drops (m : Nat) :
    acceleratedOrbit 65 (2 ^ 65 * m + 4591) < 2 ^ 65 * m + 4591 :=
  (weak_ray_stoppingTime m).2.1

/-- The endpoint retains strictly more than 98 percent of every ray member. -/
theorem weak_ray_retains_98_percent (m : Nat) :
    49 * (2 ^ 65 * m + 4591) < 50 * acceleratedOrbit 65 (2 ^ 65 * m + 4591) := by
  rw [weak_ray_endpoint, Nat.mul_add, Nat.mul_add]
  have hc : 49 * (2 : Nat) ^ 65 ≤ 50 * 3 ^ 41 := by decide
  have hm := Nat.mul_le_mul_right m hc
  rw [Nat.mul_assoc, Nat.mul_assoc] at hm
  have hb : 49 * 4591 < 50 * 4541 := by decide
  omega

/-- Weak first descents remain available above every input threshold. -/
theorem weak_drop_above_every_threshold (B : Nat) :
    ∃ n : Nat, B < n ∧ stoppingTime n 65 ∧
      49 * n < 50 * acceleratedOrbit 65 n := by
  let n := 2 ^ 65 * (B + 1) + 4591
  have hp : 0 < (2 : Nat) ^ 65 := Nat.pow_pos (by decide)
  have hm := Nat.le_mul_of_pos_left (B + 1) hp
  refine ⟨n, ?_, weak_ray_stoppingTime (B + 1), weak_ray_retains_98_percent (B + 1)⟩
  dsimp [n]
  omega

/-- No eventual two-percent first-descent contraction holds above a fixed threshold. -/
theorem no_eventual_two_percent_contraction :
    ¬ ∃ B : Nat, ∀ n k : Nat, B < n → stoppingTime n k →
      50 * acceleratedOrbit k n ≤ 49 * n := by
  rintro ⟨B, hall⟩
  obtain ⟨n, hn, hs, hweak⟩ := weak_drop_above_every_threshold B
  have h := hall n 65 hn hs
  omega

end Collatz.FirstDescentClass
