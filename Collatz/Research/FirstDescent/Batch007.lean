import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 7. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch007
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (12, 3119). -/
theorem data_12_3119 : oddCount 3119 12 = 7 ∧
    acceleratedOrbit 12 3119 = 1666 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_3119 : ∀ j : Fin 12,
    3119 ≤ acceleratedOrbit j.val 3119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_3119 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3119) = 2187 * m + 1666 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 3119
  rw [data_12_3119.1, data_12_3119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_3119 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3119) < 4096 * m + 3119 := by
  apply descent_of_endpoint
  · rw [data_12_3119.1]; exact data_12_3119.2.2
  · rw [data_12_3119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 3143). -/
theorem data_12_3143 : oddCount 3143 12 = 7 ∧
    acceleratedOrbit 12 3143 = 1679 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_3143 : ∀ j : Fin 12,
    3143 ≤ acceleratedOrbit j.val 3143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_3143 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3143) = 2187 * m + 1679 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 3143
  rw [data_12_3143.1, data_12_3143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_3143 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3143) < 4096 * m + 3143 := by
  apply descent_of_endpoint
  · rw [data_12_3143.1]; exact data_12_3143.2.2
  · rw [data_12_3143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 3295). -/
theorem data_12_3295 : oddCount 3295 12 = 7 ∧
    acceleratedOrbit 12 3295 = 1760 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_3295 : ∀ j : Fin 12,
    3295 ≤ acceleratedOrbit j.val 3295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_3295 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3295) = 2187 * m + 1760 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 3295
  rw [data_12_3295.1, data_12_3295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_3295 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3295) < 4096 * m + 3295 := by
  apply descent_of_endpoint
  · rw [data_12_3295.1]; exact data_12_3295.2.2
  · rw [data_12_3295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 3559). -/
theorem data_12_3559 : oddCount 3559 12 = 7 ∧
    acceleratedOrbit 12 3559 = 1901 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_3559 : ∀ j : Fin 12,
    3559 ≤ acceleratedOrbit j.val 3559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_3559 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3559) = 2187 * m + 1901 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 3559
  rw [data_12_3559.1, data_12_3559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_3559 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3559) < 4096 * m + 3559 := by
  apply descent_of_endpoint
  · rw [data_12_3559.1]; exact data_12_3559.2.2
  · rw [data_12_3559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 3675). -/
theorem data_12_3675 : oddCount 3675 12 = 7 ∧
    acceleratedOrbit 12 3675 = 1963 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_3675 : ∀ j : Fin 12,
    3675 ≤ acceleratedOrbit j.val 3675 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_3675 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3675) = 2187 * m + 1963 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 3675
  rw [data_12_3675.1, data_12_3675.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_3675 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3675) < 4096 * m + 3675 := by
  apply descent_of_endpoint
  · rw [data_12_3675.1]; exact data_12_3675.2.2
  · rw [data_12_3675.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 3911). -/
theorem data_12_3911 : oddCount 3911 12 = 7 ∧
    acceleratedOrbit 12 3911 = 2089 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_3911 : ∀ j : Fin 12,
    3911 ≤ acceleratedOrbit j.val 3911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_3911 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3911) = 2187 * m + 2089 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 3911
  rw [data_12_3911.1, data_12_3911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_3911 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 3911) < 4096 * m + 3911 := by
  apply descent_of_endpoint
  · rw [data_12_3911.1]; exact data_12_3911.2.2
  · rw [data_12_3911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 4063). -/
theorem data_12_4063 : oddCount 4063 12 = 7 ∧
    acceleratedOrbit 12 4063 = 2170 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_4063 : ∀ j : Fin 12,
    4063 ≤ acceleratedOrbit j.val 4063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_4063 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 4063) = 2187 * m + 2170 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 4063
  rw [data_12_4063.1, data_12_4063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_4063 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 4063) < 4096 * m + 4063 := by
  apply descent_of_endpoint
  · rw [data_12_4063.1]; exact data_12_4063.2.2
  · rw [data_12_4063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 191). -/
theorem data_13_191 : oddCount 191 13 = 8 ∧
    acceleratedOrbit 13 191 = 154 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_191 : ∀ j : Fin 13,
    191 ≤ acceleratedOrbit j.val 191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_191 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 191) = 6561 * m + 154 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 191
  rw [data_13_191.1, data_13_191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_191 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 191) < 8192 * m + 191 := by
  apply descent_of_endpoint
  · rw [data_13_191.1]; exact data_13_191.2.2
  · rw [data_13_191.2.1]; decide

end Collatz.Research.FirstDescent.Batch007
