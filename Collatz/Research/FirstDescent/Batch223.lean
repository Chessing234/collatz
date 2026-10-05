import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 223. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch223
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 7707). -/
theorem data_20_7707 : oddCount 7707 20 = 12 ∧
    acceleratedOrbit 20 7707 = 3907 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_7707 : ∀ j : Fin 20,
    7707 ≤ acceleratedOrbit j.val 7707 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_7707 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7707) = 531441 * m + 3907 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 7707
  rw [data_20_7707.1, data_20_7707.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_7707 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7707) < 1048576 * m + 7707 := by
  apply descent_of_endpoint
  · rw [data_20_7707.1]; exact data_20_7707.2.2
  · rw [data_20_7707.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 7999). -/
theorem data_20_7999 : oddCount 7999 20 = 12 ∧
    acceleratedOrbit 20 7999 = 4055 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_7999 : ∀ j : Fin 20,
    7999 ≤ acceleratedOrbit j.val 7999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_7999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7999) = 531441 * m + 4055 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 7999
  rw [data_20_7999.1, data_20_7999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_7999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7999) < 1048576 * m + 7999 := by
  apply descent_of_endpoint
  · rw [data_20_7999.1]; exact data_20_7999.2.2
  · rw [data_20_7999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 8039). -/
theorem data_20_8039 : oddCount 8039 20 = 12 ∧
    acceleratedOrbit 20 8039 = 4075 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_8039 : ∀ j : Fin 20,
    8039 ≤ acceleratedOrbit j.val 8039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_8039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8039) = 531441 * m + 4075 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 8039
  rw [data_20_8039.1, data_20_8039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_8039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8039) < 1048576 * m + 8039 := by
  apply descent_of_endpoint
  · rw [data_20_8039.1]; exact data_20_8039.2.2
  · rw [data_20_8039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 8283). -/
theorem data_20_8283 : oddCount 8283 20 = 12 ∧
    acceleratedOrbit 20 8283 = 4199 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_8283 : ∀ j : Fin 20,
    8283 ≤ acceleratedOrbit j.val 8283 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_8283 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8283) = 531441 * m + 4199 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 8283
  rw [data_20_8283.1, data_20_8283.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_8283 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8283) < 1048576 * m + 8283 := by
  apply descent_of_endpoint
  · rw [data_20_8283.1]; exact data_20_8283.2.2
  · rw [data_20_8283.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 8319). -/
theorem data_20_8319 : oddCount 8319 20 = 12 ∧
    acceleratedOrbit 20 8319 = 4217 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_8319 : ∀ j : Fin 20,
    8319 ≤ acceleratedOrbit j.val 8319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_8319 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8319) = 531441 * m + 4217 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 8319
  rw [data_20_8319.1, data_20_8319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_8319 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8319) < 1048576 * m + 8319 := by
  apply descent_of_endpoint
  · rw [data_20_8319.1]; exact data_20_8319.2.2
  · rw [data_20_8319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 8607). -/
theorem data_20_8607 : oddCount 8607 20 = 12 ∧
    acceleratedOrbit 20 8607 = 4363 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_8607 : ∀ j : Fin 20,
    8607 ≤ acceleratedOrbit j.val 8607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_8607 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8607) = 531441 * m + 4363 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 8607
  rw [data_20_8607.1, data_20_8607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_8607 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8607) < 1048576 * m + 8607 := by
  apply descent_of_endpoint
  · rw [data_20_8607.1]; exact data_20_8607.2.2
  · rw [data_20_8607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 8751). -/
theorem data_20_8751 : oddCount 8751 20 = 12 ∧
    acceleratedOrbit 20 8751 = 4436 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_8751 : ∀ j : Fin 20,
    8751 ≤ acceleratedOrbit j.val 8751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_8751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8751) = 531441 * m + 4436 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 8751
  rw [data_20_8751.1, data_20_8751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_8751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 8751) < 1048576 * m + 8751 := by
  apply descent_of_endpoint
  · rw [data_20_8751.1]; exact data_20_8751.2.2
  · rw [data_20_8751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 9023). -/
theorem data_20_9023 : oddCount 9023 20 = 12 ∧
    acceleratedOrbit 20 9023 = 4574 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_9023 : ∀ j : Fin 20,
    9023 ≤ acceleratedOrbit j.val 9023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_9023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9023) = 531441 * m + 4574 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 9023
  rw [data_20_9023.1, data_20_9023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_9023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9023) < 1048576 * m + 9023 := by
  apply descent_of_endpoint
  · rw [data_20_9023.1]; exact data_20_9023.2.2
  · rw [data_20_9023.2.1]; decide

end Collatz.Research.FirstDescent.Batch223
