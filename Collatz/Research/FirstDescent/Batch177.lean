import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 177. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch177
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 165019). -/
theorem data_18_165019 : oddCount 165019 18 = 11 ∧
    acceleratedOrbit 18 165019 = 111515 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_165019 : ∀ j : Fin 18,
    165019 ≤ acceleratedOrbit j.val 165019 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_165019 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165019) = 177147 * m + 111515 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 165019
  rw [data_18_165019.1, data_18_165019.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_165019 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165019) < 262144 * m + 165019 := by
  apply descent_of_endpoint
  · rw [data_18_165019.1]; exact data_18_165019.2.2
  · rw [data_18_165019.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 165375). -/
theorem data_18_165375 : oddCount 165375 18 = 11 ∧
    acceleratedOrbit 18 165375 = 111755 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_165375 : ∀ j : Fin 18,
    165375 ≤ acceleratedOrbit j.val 165375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_165375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165375) = 177147 * m + 111755 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 165375
  rw [data_18_165375.1, data_18_165375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_165375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165375) < 262144 * m + 165375 := by
  apply descent_of_endpoint
  · rw [data_18_165375.1]; exact data_18_165375.2.2
  · rw [data_18_165375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 165467). -/
theorem data_18_165467 : oddCount 165467 18 = 11 ∧
    acceleratedOrbit 18 165467 = 111818 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_165467 : ∀ j : Fin 18,
    165467 ≤ acceleratedOrbit j.val 165467 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_165467 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165467) = 177147 * m + 111818 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 165467
  rw [data_18_165467.1, data_18_165467.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_165467 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165467) < 262144 * m + 165467 := by
  apply descent_of_endpoint
  · rw [data_18_165467.1]; exact data_18_165467.2.2
  · rw [data_18_165467.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 165799). -/
theorem data_18_165799 : oddCount 165799 18 = 11 ∧
    acceleratedOrbit 18 165799 = 112042 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_165799 : ∀ j : Fin 18,
    165799 ≤ acceleratedOrbit j.val 165799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_165799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165799) = 177147 * m + 112042 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 165799
  rw [data_18_165799.1, data_18_165799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_165799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 165799) < 262144 * m + 165799 := by
  apply descent_of_endpoint
  · rw [data_18_165799.1]; exact data_18_165799.2.2
  · rw [data_18_165799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 166511). -/
theorem data_18_166511 : oddCount 166511 18 = 11 ∧
    acceleratedOrbit 18 166511 = 112523 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_166511 : ∀ j : Fin 18,
    166511 ≤ acceleratedOrbit j.val 166511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_166511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 166511) = 177147 * m + 112523 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 166511
  rw [data_18_166511.1, data_18_166511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_166511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 166511) < 262144 * m + 166511 := by
  apply descent_of_endpoint
  · rw [data_18_166511.1]; exact data_18_166511.2.2
  · rw [data_18_166511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 166631). -/
theorem data_18_166631 : oddCount 166631 18 = 11 ∧
    acceleratedOrbit 18 166631 = 112604 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_166631 : ∀ j : Fin 18,
    166631 ≤ acceleratedOrbit j.val 166631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_166631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 166631) = 177147 * m + 112604 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 166631
  rw [data_18_166631.1, data_18_166631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_166631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 166631) < 262144 * m + 166631 := by
  apply descent_of_endpoint
  · rw [data_18_166631.1]; exact data_18_166631.2.2
  · rw [data_18_166631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 167079). -/
theorem data_18_167079 : oddCount 167079 18 = 11 ∧
    acceleratedOrbit 18 167079 = 112907 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_167079 : ∀ j : Fin 18,
    167079 ≤ acceleratedOrbit j.val 167079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_167079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 167079) = 177147 * m + 112907 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 167079
  rw [data_18_167079.1, data_18_167079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_167079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 167079) < 262144 * m + 167079 := by
  apply descent_of_endpoint
  · rw [data_18_167079.1]; exact data_18_167079.2.2
  · rw [data_18_167079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 168095). -/
theorem data_18_168095 : oddCount 168095 18 = 11 ∧
    acceleratedOrbit 18 168095 = 113593 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_168095 : ∀ j : Fin 18,
    168095 ≤ acceleratedOrbit j.val 168095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_168095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168095) = 177147 * m + 113593 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 168095
  rw [data_18_168095.1, data_18_168095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_168095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168095) < 262144 * m + 168095 := by
  apply descent_of_endpoint
  · rw [data_18_168095.1]; exact data_18_168095.2.2
  · rw [data_18_168095.2.1]; decide

end Collatz.Research.FirstDescent.Batch177
