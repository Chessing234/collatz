import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 236. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch236
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 44391). -/
theorem data_20_44391 : oddCount 44391 20 = 12 ∧
    acceleratedOrbit 20 44391 = 22499 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_44391 : ∀ j : Fin 20,
    44391 ≤ acceleratedOrbit j.val 44391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_44391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44391) = 531441 * m + 22499 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 44391
  rw [data_20_44391.1, data_20_44391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_44391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44391) < 1048576 * m + 44391 := by
  apply descent_of_endpoint
  · rw [data_20_44391.1]; exact data_20_44391.2.2
  · rw [data_20_44391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 44527). -/
theorem data_20_44527 : oddCount 44527 20 = 12 ∧
    acceleratedOrbit 20 44527 = 22568 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_44527 : ∀ j : Fin 20,
    44527 ≤ acceleratedOrbit j.val 44527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_44527 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44527) = 531441 * m + 22568 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 44527
  rw [data_20_44527.1, data_20_44527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_44527 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44527) < 1048576 * m + 44527 := by
  apply descent_of_endpoint
  · rw [data_20_44527.1]; exact data_20_44527.2.2
  · rw [data_20_44527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 44775). -/
theorem data_20_44775 : oddCount 44775 20 = 12 ∧
    acceleratedOrbit 20 44775 = 22694 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_44775 : ∀ j : Fin 20,
    44775 ≤ acceleratedOrbit j.val 44775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_44775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44775) = 531441 * m + 22694 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 44775
  rw [data_20_44775.1, data_20_44775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_44775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44775) < 1048576 * m + 44775 := by
  apply descent_of_endpoint
  · rw [data_20_44775.1]; exact data_20_44775.2.2
  · rw [data_20_44775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 45087). -/
theorem data_20_45087 : oddCount 45087 20 = 12 ∧
    acceleratedOrbit 20 45087 = 22852 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_45087 : ∀ j : Fin 20,
    45087 ≤ acceleratedOrbit j.val 45087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_45087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 45087) = 531441 * m + 22852 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 45087
  rw [data_20_45087.1, data_20_45087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_45087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 45087) < 1048576 * m + 45087 := by
  apply descent_of_endpoint
  · rw [data_20_45087.1]; exact data_20_45087.2.2
  · rw [data_20_45087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 45551). -/
theorem data_20_45551 : oddCount 45551 20 = 12 ∧
    acceleratedOrbit 20 45551 = 23087 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_45551 : ∀ j : Fin 20,
    45551 ≤ acceleratedOrbit j.val 45551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_45551 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 45551) = 531441 * m + 23087 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 45551
  rw [data_20_45551.1, data_20_45551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_45551 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 45551) < 1048576 * m + 45551 := by
  apply descent_of_endpoint
  · rw [data_20_45551.1]; exact data_20_45551.2.2
  · rw [data_20_45551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 45567). -/
theorem data_20_45567 : oddCount 45567 20 = 12 ∧
    acceleratedOrbit 20 45567 = 23095 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_45567 : ∀ j : Fin 20,
    45567 ≤ acceleratedOrbit j.val 45567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_45567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 45567) = 531441 * m + 23095 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 45567
  rw [data_20_45567.1, data_20_45567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_45567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 45567) < 1048576 * m + 45567 := by
  apply descent_of_endpoint
  · rw [data_20_45567.1]; exact data_20_45567.2.2
  · rw [data_20_45567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 46107). -/
theorem data_20_46107 : oddCount 46107 20 = 12 ∧
    acceleratedOrbit 20 46107 = 23369 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_46107 : ∀ j : Fin 20,
    46107 ≤ acceleratedOrbit j.val 46107 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_46107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46107) = 531441 * m + 23369 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 46107
  rw [data_20_46107.1, data_20_46107.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_46107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46107) < 1048576 * m + 46107 := by
  apply descent_of_endpoint
  · rw [data_20_46107.1]; exact data_20_46107.2.2
  · rw [data_20_46107.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 46271). -/
theorem data_20_46271 : oddCount 46271 20 = 12 ∧
    acceleratedOrbit 20 46271 = 23452 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_46271 : ∀ j : Fin 20,
    46271 ≤ acceleratedOrbit j.val 46271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_46271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46271) = 531441 * m + 23452 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 46271
  rw [data_20_46271.1, data_20_46271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_46271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46271) < 1048576 * m + 46271 := by
  apply descent_of_endpoint
  · rw [data_20_46271.1]; exact data_20_46271.2.2
  · rw [data_20_46271.2.1]; decide

end Collatz.Research.FirstDescent.Batch236
