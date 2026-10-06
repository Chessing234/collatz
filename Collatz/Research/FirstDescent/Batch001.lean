import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 1. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch001
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (4, 3). -/
theorem data_4_3 : oddCount 3 4 = 2 ∧
    acceleratedOrbit 4 3 = 2 ∧ 9 < 16 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_4_3 : ∀ j : Fin 4,
    3 ≤ acceleratedOrbit j.val 3 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_4_3 (m : Nat) :
    acceleratedOrbit 4 (16 * m + 3) = 9 * m + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 m 3
  rw [data_4_3.1, data_4_3.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_4_3 (m : Nat) :
    acceleratedOrbit 4 (16 * m + 3) < 16 * m + 3 := by
  apply descent_of_endpoint
  · rw [data_4_3.1]; exact data_4_3.2.2
  · rw [data_4_3.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (5, 11). -/
theorem data_5_11 : oddCount 11 5 = 3 ∧
    acceleratedOrbit 5 11 = 10 ∧ 27 < 32 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_5_11 : ∀ j : Fin 5,
    11 ≤ acceleratedOrbit j.val 11 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_5_11 (m : Nat) :
    acceleratedOrbit 5 (32 * m + 11) = 27 * m + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 m 11
  rw [data_5_11.1, data_5_11.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_5_11 (m : Nat) :
    acceleratedOrbit 5 (32 * m + 11) < 32 * m + 11 := by
  apply descent_of_endpoint
  · rw [data_5_11.1]; exact data_5_11.2.2
  · rw [data_5_11.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (5, 23). -/
theorem data_5_23 : oddCount 23 5 = 3 ∧
    acceleratedOrbit 5 23 = 20 ∧ 27 < 32 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_5_23 : ∀ j : Fin 5,
    23 ≤ acceleratedOrbit j.val 23 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_5_23 (m : Nat) :
    acceleratedOrbit 5 (32 * m + 23) = 27 * m + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 m 23
  rw [data_5_23.1, data_5_23.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_5_23 (m : Nat) :
    acceleratedOrbit 5 (32 * m + 23) < 32 * m + 23 := by
  apply descent_of_endpoint
  · rw [data_5_23.1]; exact data_5_23.2.2
  · rw [data_5_23.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (7, 7). -/
theorem data_7_7 : oddCount 7 7 = 4 ∧
    acceleratedOrbit 7 7 = 5 ∧ 81 < 128 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_7_7 : ∀ j : Fin 7,
    7 ≤ acceleratedOrbit j.val 7 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_7_7 (m : Nat) :
    acceleratedOrbit 7 (128 * m + 7) = 81 * m + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 m 7
  rw [data_7_7.1, data_7_7.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_7_7 (m : Nat) :
    acceleratedOrbit 7 (128 * m + 7) < 128 * m + 7 := by
  apply descent_of_endpoint
  · rw [data_7_7.1]; exact data_7_7.2.2
  · rw [data_7_7.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (7, 15). -/
theorem data_7_15 : oddCount 15 7 = 4 ∧
    acceleratedOrbit 7 15 = 10 ∧ 81 < 128 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_7_15 : ∀ j : Fin 7,
    15 ≤ acceleratedOrbit j.val 15 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_7_15 (m : Nat) :
    acceleratedOrbit 7 (128 * m + 15) = 81 * m + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 m 15
  rw [data_7_15.1, data_7_15.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_7_15 (m : Nat) :
    acceleratedOrbit 7 (128 * m + 15) < 128 * m + 15 := by
  apply descent_of_endpoint
  · rw [data_7_15.1]; exact data_7_15.2.2
  · rw [data_7_15.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (7, 59). -/
theorem data_7_59 : oddCount 59 7 = 4 ∧
    acceleratedOrbit 7 59 = 38 ∧ 81 < 128 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_7_59 : ∀ j : Fin 7,
    59 ≤ acceleratedOrbit j.val 59 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_7_59 (m : Nat) :
    acceleratedOrbit 7 (128 * m + 59) = 81 * m + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 m 59
  rw [data_7_59.1, data_7_59.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_7_59 (m : Nat) :
    acceleratedOrbit 7 (128 * m + 59) < 128 * m + 59 := by
  apply descent_of_endpoint
  · rw [data_7_59.1]; exact data_7_59.2.2
  · rw [data_7_59.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (8, 39). -/
theorem data_8_39 : oddCount 39 8 = 5 ∧
    acceleratedOrbit 8 39 = 38 ∧ 243 < 256 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_8_39 : ∀ j : Fin 8,
    39 ≤ acceleratedOrbit j.val 39 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_8_39 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 39) = 243 * m + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 m 39
  rw [data_8_39.1, data_8_39.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_8_39 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 39) < 256 * m + 39 := by
  apply descent_of_endpoint
  · rw [data_8_39.1]; exact data_8_39.2.2
  · rw [data_8_39.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (8, 79). -/
theorem data_8_79 : oddCount 79 8 = 5 ∧
    acceleratedOrbit 8 79 = 76 ∧ 243 < 256 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_8_79 : ∀ j : Fin 8,
    79 ≤ acceleratedOrbit j.val 79 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_8_79 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 79) = 243 * m + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 m 79
  rw [data_8_79.1, data_8_79.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_8_79 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 79) < 256 * m + 79 := by
  apply descent_of_endpoint
  · rw [data_8_79.1]; exact data_8_79.2.2
  · rw [data_8_79.2.1]; decide

end Collatz.Research.FirstDescent.Batch001
