import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 159. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch159
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 123163). -/
theorem data_18_123163 : oddCount 123163 18 = 11 ∧
    acceleratedOrbit 18 123163 = 83230 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_123163 : ∀ j : Fin 18,
    123163 ≤ acceleratedOrbit j.val 123163 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_123163 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123163) = 177147 * m + 83230 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 123163
  rw [data_18_123163.1, data_18_123163.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_123163 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123163) < 262144 * m + 123163 := by
  apply descent_of_endpoint
  · rw [data_18_123163.1]; exact data_18_123163.2.2
  · rw [data_18_123163.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 123367). -/
theorem data_18_123367 : oddCount 123367 18 = 11 ∧
    acceleratedOrbit 18 123367 = 83368 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_123367 : ∀ j : Fin 18,
    123367 ≤ acceleratedOrbit j.val 123367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_123367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123367) = 177147 * m + 83368 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 123367
  rw [data_18_123367.1, data_18_123367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_123367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123367) < 262144 * m + 123367 := by
  apply descent_of_endpoint
  · rw [data_18_123367.1]; exact data_18_123367.2.2
  · rw [data_18_123367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 123631). -/
theorem data_18_123631 : oddCount 123631 18 = 11 ∧
    acceleratedOrbit 18 123631 = 83546 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_123631 : ∀ j : Fin 18,
    123631 ≤ acceleratedOrbit j.val 123631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_123631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123631) = 177147 * m + 83546 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 123631
  rw [data_18_123631.1, data_18_123631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_123631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123631) < 262144 * m + 123631 := by
  apply descent_of_endpoint
  · rw [data_18_123631.1]; exact data_18_123631.2.2
  · rw [data_18_123631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 123675). -/
theorem data_18_123675 : oddCount 123675 18 = 11 ∧
    acceleratedOrbit 18 123675 = 83576 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_123675 : ∀ j : Fin 18,
    123675 ≤ acceleratedOrbit j.val 123675 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_123675 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123675) = 177147 * m + 83576 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 123675
  rw [data_18_123675.1, data_18_123675.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_123675 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123675) < 262144 * m + 123675 := by
  apply descent_of_endpoint
  · rw [data_18_123675.1]; exact data_18_123675.2.2
  · rw [data_18_123675.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 123719). -/
theorem data_18_123719 : oddCount 123719 18 = 11 ∧
    acceleratedOrbit 18 123719 = 83606 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_123719 : ∀ j : Fin 18,
    123719 ≤ acceleratedOrbit j.val 123719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_123719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123719) = 177147 * m + 83606 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 123719
  rw [data_18_123719.1, data_18_123719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_123719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123719) < 262144 * m + 123719 := by
  apply descent_of_endpoint
  · rw [data_18_123719.1]; exact data_18_123719.2.2
  · rw [data_18_123719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 124319). -/
theorem data_18_124319 : oddCount 124319 18 = 11 ∧
    acceleratedOrbit 18 124319 = 84011 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_124319 : ∀ j : Fin 18,
    124319 ≤ acceleratedOrbit j.val 124319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_124319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 124319) = 177147 * m + 84011 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 124319
  rw [data_18_124319.1, data_18_124319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_124319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 124319) < 262144 * m + 124319 := by
  apply descent_of_endpoint
  · rw [data_18_124319.1]; exact data_18_124319.2.2
  · rw [data_18_124319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 124367). -/
theorem data_18_124367 : oddCount 124367 18 = 11 ∧
    acceleratedOrbit 18 124367 = 84044 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_124367 : ∀ j : Fin 18,
    124367 ≤ acceleratedOrbit j.val 124367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_124367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 124367) = 177147 * m + 84044 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 124367
  rw [data_18_124367.1, data_18_124367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_124367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 124367) < 262144 * m + 124367 := by
  apply descent_of_endpoint
  · rw [data_18_124367.1]; exact data_18_124367.2.2
  · rw [data_18_124367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 124647). -/
theorem data_18_124647 : oddCount 124647 18 = 11 ∧
    acceleratedOrbit 18 124647 = 84233 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_124647 : ∀ j : Fin 18,
    124647 ≤ acceleratedOrbit j.val 124647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_124647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 124647) = 177147 * m + 84233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 124647
  rw [data_18_124647.1, data_18_124647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_124647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 124647) < 262144 * m + 124647 := by
  apply descent_of_endpoint
  · rw [data_18_124647.1]; exact data_18_124647.2.2
  · rw [data_18_124647.2.1]; decide

end Collatz.Research.FirstDescent.Batch159
