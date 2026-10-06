import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 237. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch237
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 46383). -/
theorem data_20_46383 : oddCount 46383 20 = 12 ∧
    acceleratedOrbit 20 46383 = 23509 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_46383 : ∀ j : Fin 20,
    46383 ≤ acceleratedOrbit j.val 46383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_46383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46383) = 531441 * m + 23509 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 46383
  rw [data_20_46383.1, data_20_46383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_46383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46383) < 1048576 * m + 46383 := by
  apply descent_of_endpoint
  · rw [data_20_46383.1]; exact data_20_46383.2.2
  · rw [data_20_46383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 46543). -/
theorem data_20_46543 : oddCount 46543 20 = 12 ∧
    acceleratedOrbit 20 46543 = 23590 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_46543 : ∀ j : Fin 20,
    46543 ≤ acceleratedOrbit j.val 46543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_46543 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46543) = 531441 * m + 23590 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 46543
  rw [data_20_46543.1, data_20_46543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_46543 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46543) < 1048576 * m + 46543 := by
  apply descent_of_endpoint
  · rw [data_20_46543.1]; exact data_20_46543.2.2
  · rw [data_20_46543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 46591). -/
theorem data_20_46591 : oddCount 46591 20 = 12 ∧
    acceleratedOrbit 20 46591 = 23614 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_46591 : ∀ j : Fin 20,
    46591 ≤ acceleratedOrbit j.val 46591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_46591 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46591) = 531441 * m + 23614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 46591
  rw [data_20_46591.1, data_20_46591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_46591 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46591) < 1048576 * m + 46591 := by
  apply descent_of_endpoint
  · rw [data_20_46591.1]; exact data_20_46591.2.2
  · rw [data_20_46591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 46875). -/
theorem data_20_46875 : oddCount 46875 20 = 12 ∧
    acceleratedOrbit 20 46875 = 23758 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_46875 : ∀ j : Fin 20,
    46875 ≤ acceleratedOrbit j.val 46875 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_46875 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46875) = 531441 * m + 23758 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 46875
  rw [data_20_46875.1, data_20_46875.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_46875 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 46875) < 1048576 * m + 46875 := by
  apply descent_of_endpoint
  · rw [data_20_46875.1]; exact data_20_46875.2.2
  · rw [data_20_46875.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 47271). -/
theorem data_20_47271 : oddCount 47271 20 = 12 ∧
    acceleratedOrbit 20 47271 = 23959 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_47271 : ∀ j : Fin 20,
    47271 ≤ acceleratedOrbit j.val 47271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_47271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 47271) = 531441 * m + 23959 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 47271
  rw [data_20_47271.1, data_20_47271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_47271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 47271) < 1048576 * m + 47271 := by
  apply descent_of_endpoint
  · rw [data_20_47271.1]; exact data_20_47271.2.2
  · rw [data_20_47271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 47599). -/
theorem data_20_47599 : oddCount 47599 20 = 12 ∧
    acceleratedOrbit 20 47599 = 24125 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_47599 : ∀ j : Fin 20,
    47599 ≤ acceleratedOrbit j.val 47599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_47599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 47599) = 531441 * m + 24125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 47599
  rw [data_20_47599.1, data_20_47599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_47599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 47599) < 1048576 * m + 47599 := by
  apply descent_of_endpoint
  · rw [data_20_47599.1]; exact data_20_47599.2.2
  · rw [data_20_47599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 47899). -/
theorem data_20_47899 : oddCount 47899 20 = 12 ∧
    acceleratedOrbit 20 47899 = 24277 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_47899 : ∀ j : Fin 20,
    47899 ≤ acceleratedOrbit j.val 47899 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_47899 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 47899) = 531441 * m + 24277 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 47899
  rw [data_20_47899.1, data_20_47899.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_47899 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 47899) < 1048576 * m + 47899 := by
  apply descent_of_endpoint
  · rw [data_20_47899.1]; exact data_20_47899.2.2
  · rw [data_20_47899.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 48283). -/
theorem data_20_48283 : oddCount 48283 20 = 12 ∧
    acceleratedOrbit 20 48283 = 24472 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_48283 : ∀ j : Fin 20,
    48283 ≤ acceleratedOrbit j.val 48283 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_48283 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 48283) = 531441 * m + 24472 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 48283
  rw [data_20_48283.1, data_20_48283.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_48283 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 48283) < 1048576 * m + 48283 := by
  apply descent_of_endpoint
  · rw [data_20_48283.1]; exact data_20_48283.2.2
  · rw [data_20_48283.2.1]; decide

end Collatz.Research.FirstDescent.Batch237
