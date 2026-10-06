import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 252. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch252
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 90395). -/
theorem data_20_90395 : oddCount 90395 20 = 12 ∧
    acceleratedOrbit 20 90395 = 45815 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_90395 : ∀ j : Fin 20,
    90395 ≤ acceleratedOrbit j.val 90395 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_90395 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90395) = 531441 * m + 45815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 90395
  rw [data_20_90395.1, data_20_90395.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_90395 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90395) < 1048576 * m + 90395 := by
  apply descent_of_endpoint
  · rw [data_20_90395.1]; exact data_20_90395.2.2
  · rw [data_20_90395.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 90863). -/
theorem data_20_90863 : oddCount 90863 20 = 12 ∧
    acceleratedOrbit 20 90863 = 46052 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_90863 : ∀ j : Fin 20,
    90863 ≤ acceleratedOrbit j.val 90863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_90863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90863) = 531441 * m + 46052 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 90863
  rw [data_20_90863.1, data_20_90863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_90863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90863) < 1048576 * m + 90863 := by
  apply descent_of_endpoint
  · rw [data_20_90863.1]; exact data_20_90863.2.2
  · rw [data_20_90863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 90879). -/
theorem data_20_90879 : oddCount 90879 20 = 12 ∧
    acceleratedOrbit 20 90879 = 46060 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_90879 : ∀ j : Fin 20,
    90879 ≤ acceleratedOrbit j.val 90879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_90879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90879) = 531441 * m + 46060 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 90879
  rw [data_20_90879.1, data_20_90879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_90879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90879) < 1048576 * m + 90879 := by
  apply descent_of_endpoint
  · rw [data_20_90879.1]; exact data_20_90879.2.2
  · rw [data_20_90879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 91419). -/
theorem data_20_91419 : oddCount 91419 20 = 12 ∧
    acceleratedOrbit 20 91419 = 46334 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_91419 : ∀ j : Fin 20,
    91419 ≤ acceleratedOrbit j.val 91419 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_91419 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 91419) = 531441 * m + 46334 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 91419
  rw [data_20_91419.1, data_20_91419.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_91419 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 91419) < 1048576 * m + 91419 := by
  apply descent_of_endpoint
  · rw [data_20_91419.1]; exact data_20_91419.2.2
  · rw [data_20_91419.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 91855). -/
theorem data_20_91855 : oddCount 91855 20 = 12 ∧
    acceleratedOrbit 20 91855 = 46555 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_91855 : ∀ j : Fin 20,
    91855 ≤ acceleratedOrbit j.val 91855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_91855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 91855) = 531441 * m + 46555 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 91855
  rw [data_20_91855.1, data_20_91855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_91855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 91855) < 1048576 * m + 91855 := by
  apply descent_of_endpoint
  · rw [data_20_91855.1]; exact data_20_91855.2.2
  · rw [data_20_91855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 92411). -/
theorem data_20_92411 : oddCount 92411 20 = 12 ∧
    acceleratedOrbit 20 92411 = 46837 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_92411 : ∀ j : Fin 20,
    92411 ≤ acceleratedOrbit j.val 92411 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_92411 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 92411) = 531441 * m + 46837 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 92411
  rw [data_20_92411.1, data_20_92411.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_92411 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 92411) < 1048576 * m + 92411 := by
  apply descent_of_endpoint
  · rw [data_20_92411.1]; exact data_20_92411.2.2
  · rw [data_20_92411.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 92571). -/
theorem data_20_92571 : oddCount 92571 20 = 12 ∧
    acceleratedOrbit 20 92571 = 46918 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_92571 : ∀ j : Fin 20,
    92571 ≤ acceleratedOrbit j.val 92571 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_92571 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 92571) = 531441 * m + 46918 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 92571
  rw [data_20_92571.1, data_20_92571.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_92571 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 92571) < 1048576 * m + 92571 := by
  apply descent_of_endpoint
  · rw [data_20_92571.1]; exact data_20_92571.2.2
  · rw [data_20_92571.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 92903). -/
theorem data_20_92903 : oddCount 92903 20 = 12 ∧
    acceleratedOrbit 20 92903 = 47086 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_92903 : ∀ j : Fin 20,
    92903 ≤ acceleratedOrbit j.val 92903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_92903 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 92903) = 531441 * m + 47086 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 92903
  rw [data_20_92903.1, data_20_92903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_92903 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 92903) < 1048576 * m + 92903 := by
  apply descent_of_endpoint
  · rw [data_20_92903.1]; exact data_20_92903.2.2
  · rw [data_20_92903.2.1]; decide

end Collatz.Research.FirstDescent.Batch252
