import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 149. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch149
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105247). -/
theorem data_18_105247 : oddCount 105247 18 = 11 ∧
    acceleratedOrbit 18 105247 = 71123 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105247 : ∀ j : Fin 18,
    105247 ≤ acceleratedOrbit j.val 105247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105247 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105247) = 177147 * m + 71123 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105247
  rw [data_18_105247.1, data_18_105247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105247 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105247) < 262144 * m + 105247 := by
  apply descent_of_endpoint
  · rw [data_18_105247.1]; exact data_18_105247.2.2
  · rw [data_18_105247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105407). -/
theorem data_18_105407 : oddCount 105407 18 = 11 ∧
    acceleratedOrbit 18 105407 = 71231 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105407 : ∀ j : Fin 18,
    105407 ≤ acceleratedOrbit j.val 105407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105407) = 177147 * m + 71231 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105407
  rw [data_18_105407.1, data_18_105407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105407) < 262144 * m + 105407 := by
  apply descent_of_endpoint
  · rw [data_18_105407.1]; exact data_18_105407.2.2
  · rw [data_18_105407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105535). -/
theorem data_18_105535 : oddCount 105535 18 = 11 ∧
    acceleratedOrbit 18 105535 = 71318 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105535 : ∀ j : Fin 18,
    105535 ≤ acceleratedOrbit j.val 105535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105535) = 177147 * m + 71318 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105535
  rw [data_18_105535.1, data_18_105535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105535) < 262144 * m + 105535 := by
  apply descent_of_endpoint
  · rw [data_18_105535.1]; exact data_18_105535.2.2
  · rw [data_18_105535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105583). -/
theorem data_18_105583 : oddCount 105583 18 = 11 ∧
    acceleratedOrbit 18 105583 = 71350 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105583 : ∀ j : Fin 18,
    105583 ≤ acceleratedOrbit j.val 105583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105583) = 177147 * m + 71350 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105583
  rw [data_18_105583.1, data_18_105583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105583) < 262144 * m + 105583 := by
  apply descent_of_endpoint
  · rw [data_18_105583.1]; exact data_18_105583.2.2
  · rw [data_18_105583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105627). -/
theorem data_18_105627 : oddCount 105627 18 = 11 ∧
    acceleratedOrbit 18 105627 = 71380 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105627 : ∀ j : Fin 18,
    105627 ≤ acceleratedOrbit j.val 105627 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105627 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105627) = 177147 * m + 71380 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105627
  rw [data_18_105627.1, data_18_105627.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105627 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105627) < 262144 * m + 105627 := by
  apply descent_of_endpoint
  · rw [data_18_105627.1]; exact data_18_105627.2.2
  · rw [data_18_105627.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105663). -/
theorem data_18_105663 : oddCount 105663 18 = 11 ∧
    acceleratedOrbit 18 105663 = 71404 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105663 : ∀ j : Fin 18,
    105663 ≤ acceleratedOrbit j.val 105663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105663) = 177147 * m + 71404 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105663
  rw [data_18_105663.1, data_18_105663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105663) < 262144 * m + 105663 := by
  apply descent_of_endpoint
  · rw [data_18_105663.1]; exact data_18_105663.2.2
  · rw [data_18_105663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105775). -/
theorem data_18_105775 : oddCount 105775 18 = 11 ∧
    acceleratedOrbit 18 105775 = 71480 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105775 : ∀ j : Fin 18,
    105775 ≤ acceleratedOrbit j.val 105775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105775) = 177147 * m + 71480 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105775
  rw [data_18_105775.1, data_18_105775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105775) < 262144 * m + 105775 := by
  apply descent_of_endpoint
  · rw [data_18_105775.1]; exact data_18_105775.2.2
  · rw [data_18_105775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105855). -/
theorem data_18_105855 : oddCount 105855 18 = 11 ∧
    acceleratedOrbit 18 105855 = 71534 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105855 : ∀ j : Fin 18,
    105855 ≤ acceleratedOrbit j.val 105855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105855) = 177147 * m + 71534 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105855
  rw [data_18_105855.1, data_18_105855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105855) < 262144 * m + 105855 := by
  apply descent_of_endpoint
  · rw [data_18_105855.1]; exact data_18_105855.2.2
  · rw [data_18_105855.2.1]; decide

end Collatz.Research.FirstDescent.Batch149
