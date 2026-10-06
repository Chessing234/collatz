import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 16. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch016
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6375). -/
theorem data_13_6375 : oddCount 6375 13 = 8 ∧
    acceleratedOrbit 13 6375 = 5107 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6375 : ∀ j : Fin 13,
    6375 ≤ acceleratedOrbit j.val 6375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6375 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6375) = 6561 * m + 5107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6375
  rw [data_13_6375.1, data_13_6375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6375 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6375) < 8192 * m + 6375 := by
  apply descent_of_endpoint
  · rw [data_13_6375.1]; exact data_13_6375.2.2
  · rw [data_13_6375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6559). -/
theorem data_13_6559 : oddCount 6559 13 = 8 ∧
    acceleratedOrbit 13 6559 = 5254 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6559 : ∀ j : Fin 13,
    6559 ≤ acceleratedOrbit j.val 6559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6559 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6559) = 6561 * m + 5254 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6559
  rw [data_13_6559.1, data_13_6559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6559 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6559) < 8192 * m + 6559 := by
  apply descent_of_endpoint
  · rw [data_13_6559.1]; exact data_13_6559.2.2
  · rw [data_13_6559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6607). -/
theorem data_13_6607 : oddCount 6607 13 = 8 ∧
    acceleratedOrbit 13 6607 = 5293 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6607 : ∀ j : Fin 13,
    6607 ≤ acceleratedOrbit j.val 6607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6607 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6607) = 6561 * m + 5293 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6607
  rw [data_13_6607.1, data_13_6607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6607 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6607) < 8192 * m + 6607 := by
  apply descent_of_endpoint
  · rw [data_13_6607.1]; exact data_13_6607.2.2
  · rw [data_13_6607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6631). -/
theorem data_13_6631 : oddCount 6631 13 = 8 ∧
    acceleratedOrbit 13 6631 = 5312 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6631 : ∀ j : Fin 13,
    6631 ≤ acceleratedOrbit j.val 6631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6631 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6631) = 6561 * m + 5312 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6631
  rw [data_13_6631.1, data_13_6631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6631 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6631) < 8192 * m + 6631 := by
  apply descent_of_endpoint
  · rw [data_13_6631.1]; exact data_13_6631.2.2
  · rw [data_13_6631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6747). -/
theorem data_13_6747 : oddCount 6747 13 = 8 ∧
    acceleratedOrbit 13 6747 = 5405 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6747 : ∀ j : Fin 13,
    6747 ≤ acceleratedOrbit j.val 6747 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6747 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6747) = 6561 * m + 5405 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6747
  rw [data_13_6747.1, data_13_6747.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6747 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6747) < 8192 * m + 6747 := by
  apply descent_of_endpoint
  · rw [data_13_6747.1]; exact data_13_6747.2.2
  · rw [data_13_6747.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6815). -/
theorem data_13_6815 : oddCount 6815 13 = 8 ∧
    acceleratedOrbit 13 6815 = 5459 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6815 : ∀ j : Fin 13,
    6815 ≤ acceleratedOrbit j.val 6815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6815 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6815) = 6561 * m + 5459 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6815
  rw [data_13_6815.1, data_13_6815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6815 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6815) < 8192 * m + 6815 := by
  apply descent_of_endpoint
  · rw [data_13_6815.1]; exact data_13_6815.2.2
  · rw [data_13_6815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6983). -/
theorem data_13_6983 : oddCount 6983 13 = 8 ∧
    acceleratedOrbit 13 6983 = 5594 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6983 : ∀ j : Fin 13,
    6983 ≤ acceleratedOrbit j.val 6983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6983 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6983) = 6561 * m + 5594 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6983
  rw [data_13_6983.1, data_13_6983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6983 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6983) < 8192 * m + 6983 := by
  apply descent_of_endpoint
  · rw [data_13_6983.1]; exact data_13_6983.2.2
  · rw [data_13_6983.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7023). -/
theorem data_13_7023 : oddCount 7023 13 = 8 ∧
    acceleratedOrbit 13 7023 = 5626 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7023 : ∀ j : Fin 13,
    7023 ≤ acceleratedOrbit j.val 7023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7023 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7023) = 6561 * m + 5626 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7023
  rw [data_13_7023.1, data_13_7023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7023 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7023) < 8192 * m + 7023 := by
  apply descent_of_endpoint
  · rw [data_13_7023.1]; exact data_13_7023.2.2
  · rw [data_13_7023.2.1]; decide

end Collatz.Research.FirstDescent.Batch016
