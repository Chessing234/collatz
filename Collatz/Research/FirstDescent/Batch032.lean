import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 32. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch032
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 20507). -/
theorem data_15_20507 : oddCount 20507 15 = 9 ∧
    acceleratedOrbit 15 20507 = 12319 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_20507 : ∀ j : Fin 15,
    20507 ≤ acceleratedOrbit j.val 20507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_20507 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20507) = 19683 * m + 12319 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 20507
  rw [data_15_20507.1, data_15_20507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_20507 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20507) < 32768 * m + 20507 := by
  apply descent_of_endpoint
  · rw [data_15_20507.1]; exact data_15_20507.2.2
  · rw [data_15_20507.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 20527). -/
theorem data_15_20527 : oddCount 20527 15 = 9 ∧
    acceleratedOrbit 15 20527 = 12331 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_20527 : ∀ j : Fin 15,
    20527 ≤ acceleratedOrbit j.val 20527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_20527 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20527) = 19683 * m + 12331 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 20527
  rw [data_15_20527.1, data_15_20527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_20527 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20527) < 32768 * m + 20527 := by
  apply descent_of_endpoint
  · rw [data_15_20527.1]; exact data_15_20527.2.2
  · rw [data_15_20527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 20783). -/
theorem data_15_20783 : oddCount 20783 15 = 9 ∧
    acceleratedOrbit 15 20783 = 12485 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_20783 : ∀ j : Fin 15,
    20783 ≤ acceleratedOrbit j.val 20783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_20783 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20783) = 19683 * m + 12485 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 20783
  rw [data_15_20783.1, data_15_20783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_20783 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20783) < 32768 * m + 20783 := by
  apply descent_of_endpoint
  · rw [data_15_20783.1]; exact data_15_20783.2.2
  · rw [data_15_20783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 20927). -/
theorem data_15_20927 : oddCount 20927 15 = 9 ∧
    acceleratedOrbit 15 20927 = 12571 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_20927 : ∀ j : Fin 15,
    20927 ≤ acceleratedOrbit j.val 20927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_20927 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20927) = 19683 * m + 12571 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 20927
  rw [data_15_20927.1, data_15_20927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_20927 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20927) < 32768 * m + 20927 := by
  apply descent_of_endpoint
  · rw [data_15_20927.1]; exact data_15_20927.2.2
  · rw [data_15_20927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 21023). -/
theorem data_15_21023 : oddCount 21023 15 = 9 ∧
    acceleratedOrbit 15 21023 = 12629 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_21023 : ∀ j : Fin 15,
    21023 ≤ acceleratedOrbit j.val 21023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_21023 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21023) = 19683 * m + 12629 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 21023
  rw [data_15_21023.1, data_15_21023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_21023 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21023) < 32768 * m + 21023 := by
  apply descent_of_endpoint
  · rw [data_15_21023.1]; exact data_15_21023.2.2
  · rw [data_15_21023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 21103). -/
theorem data_15_21103 : oddCount 21103 15 = 9 ∧
    acceleratedOrbit 15 21103 = 12677 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_21103 : ∀ j : Fin 15,
    21103 ≤ acceleratedOrbit j.val 21103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_21103 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21103) = 19683 * m + 12677 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 21103
  rw [data_15_21103.1, data_15_21103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_21103 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21103) < 32768 * m + 21103 := by
  apply descent_of_endpoint
  · rw [data_15_21103.1]; exact data_15_21103.2.2
  · rw [data_15_21103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 21223). -/
theorem data_15_21223 : oddCount 21223 15 = 9 ∧
    acceleratedOrbit 15 21223 = 12749 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_21223 : ∀ j : Fin 15,
    21223 ≤ acceleratedOrbit j.val 21223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_21223 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21223) = 19683 * m + 12749 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 21223
  rw [data_15_21223.1, data_15_21223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_21223 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21223) < 32768 * m + 21223 := by
  apply descent_of_endpoint
  · rw [data_15_21223.1]; exact data_15_21223.2.2
  · rw [data_15_21223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 21471). -/
theorem data_15_21471 : oddCount 21471 15 = 9 ∧
    acceleratedOrbit 15 21471 = 12898 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_21471 : ∀ j : Fin 15,
    21471 ≤ acceleratedOrbit j.val 21471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_21471 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21471) = 19683 * m + 12898 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 21471
  rw [data_15_21471.1, data_15_21471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_21471 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21471) < 32768 * m + 21471 := by
  apply descent_of_endpoint
  · rw [data_15_21471.1]; exact data_15_21471.2.2
  · rw [data_15_21471.2.1]; decide

end Collatz.Research.FirstDescent.Batch032
