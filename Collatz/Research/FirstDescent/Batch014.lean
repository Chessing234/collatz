import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 14. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch014
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4955). -/
theorem data_13_4955 : oddCount 4955 13 = 8 ∧
    acceleratedOrbit 13 4955 = 3970 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4955 : ∀ j : Fin 13,
    4955 ≤ acceleratedOrbit j.val 4955 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4955 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4955) = 6561 * m + 3970 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4955
  rw [data_13_4955.1, data_13_4955.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4955 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4955) < 8192 * m + 4955 := by
  apply descent_of_endpoint
  · rw [data_13_4955.1]; exact data_13_4955.2.2
  · rw [data_13_4955.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5023). -/
theorem data_13_5023 : oddCount 5023 13 = 8 ∧
    acceleratedOrbit 13 5023 = 4024 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5023 : ∀ j : Fin 13,
    5023 ≤ acceleratedOrbit j.val 5023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5023 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5023) = 6561 * m + 4024 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5023
  rw [data_13_5023.1, data_13_5023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5023 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5023) < 8192 * m + 5023 := by
  apply descent_of_endpoint
  · rw [data_13_5023.1]; exact data_13_5023.2.2
  · rw [data_13_5023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5103). -/
theorem data_13_5103 : oddCount 5103 13 = 8 ∧
    acceleratedOrbit 13 5103 = 4088 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5103 : ∀ j : Fin 13,
    5103 ≤ acceleratedOrbit j.val 5103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5103 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5103) = 6561 * m + 4088 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5103
  rw [data_13_5103.1, data_13_5103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5103 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5103) < 8192 * m + 5103 := by
  apply descent_of_endpoint
  · rw [data_13_5103.1]; exact data_13_5103.2.2
  · rw [data_13_5103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5191). -/
theorem data_13_5191 : oddCount 5191 13 = 8 ∧
    acceleratedOrbit 13 5191 = 4159 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5191 : ∀ j : Fin 13,
    5191 ≤ acceleratedOrbit j.val 5191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5191 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5191) = 6561 * m + 4159 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5191
  rw [data_13_5191.1, data_13_5191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5191 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5191) < 8192 * m + 5191 := by
  apply descent_of_endpoint
  · rw [data_13_5191.1]; exact data_13_5191.2.2
  · rw [data_13_5191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5275). -/
theorem data_13_5275 : oddCount 5275 13 = 8 ∧
    acceleratedOrbit 13 5275 = 4226 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5275 : ∀ j : Fin 13,
    5275 ≤ acceleratedOrbit j.val 5275 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5275 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5275) = 6561 * m + 4226 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5275
  rw [data_13_5275.1, data_13_5275.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5275 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5275) < 8192 * m + 5275 := by
  apply descent_of_endpoint
  · rw [data_13_5275.1]; exact data_13_5275.2.2
  · rw [data_13_5275.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5371). -/
theorem data_13_5371 : oddCount 5371 13 = 8 ∧
    acceleratedOrbit 13 5371 = 4303 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5371 : ∀ j : Fin 13,
    5371 ≤ acceleratedOrbit j.val 5371 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5371 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5371) = 6561 * m + 4303 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5371
  rw [data_13_5371.1, data_13_5371.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5371 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5371) < 8192 * m + 5371 := by
  apply descent_of_endpoint
  · rw [data_13_5371.1]; exact data_13_5371.2.2
  · rw [data_13_5371.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5439). -/
theorem data_13_5439 : oddCount 5439 13 = 8 ∧
    acceleratedOrbit 13 5439 = 4357 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5439 : ∀ j : Fin 13,
    5439 ≤ acceleratedOrbit j.val 5439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5439 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5439) = 6561 * m + 4357 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5439
  rw [data_13_5439.1, data_13_5439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5439 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5439) < 8192 * m + 5439 := by
  apply descent_of_endpoint
  · rw [data_13_5439.1]; exact data_13_5439.2.2
  · rw [data_13_5439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5607). -/
theorem data_13_5607 : oddCount 5607 13 = 8 ∧
    acceleratedOrbit 13 5607 = 4492 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5607 : ∀ j : Fin 13,
    5607 ≤ acceleratedOrbit j.val 5607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5607 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5607) = 6561 * m + 4492 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5607
  rw [data_13_5607.1, data_13_5607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5607 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5607) < 8192 * m + 5607 := by
  apply descent_of_endpoint
  · rw [data_13_5607.1]; exact data_13_5607.2.2
  · rw [data_13_5607.2.1]; decide

end Collatz.Research.FirstDescent.Batch014
