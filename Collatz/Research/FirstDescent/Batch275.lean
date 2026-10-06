import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 275. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch275
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 168219). -/
theorem data_20_168219 : oddCount 168219 20 = 12 ∧
    acceleratedOrbit 20 168219 = 85258 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_168219 : ∀ j : Fin 20,
    168219 ≤ acceleratedOrbit j.val 168219 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_168219 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168219) = 531441 * m + 85258 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 168219
  rw [data_20_168219.1, data_20_168219.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_168219 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168219) < 1048576 * m + 168219 := by
  apply descent_of_endpoint
  · rw [data_20_168219.1]; exact data_20_168219.2.2
  · rw [data_20_168219.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 168475). -/
theorem data_20_168475 : oddCount 168475 20 = 12 ∧
    acceleratedOrbit 20 168475 = 85388 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_168475 : ∀ j : Fin 20,
    168475 ≤ acceleratedOrbit j.val 168475 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_168475 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168475) = 531441 * m + 85388 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 168475
  rw [data_20_168475.1, data_20_168475.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_168475 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168475) < 1048576 * m + 168475 := by
  apply descent_of_endpoint
  · rw [data_20_168475.1]; exact data_20_168475.2.2
  · rw [data_20_168475.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 168831). -/
theorem data_20_168831 : oddCount 168831 20 = 12 ∧
    acceleratedOrbit 20 168831 = 85568 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_168831 : ∀ j : Fin 20,
    168831 ≤ acceleratedOrbit j.val 168831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_168831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168831) = 531441 * m + 85568 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 168831
  rw [data_20_168831.1, data_20_168831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_168831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168831) < 1048576 * m + 168831 := by
  apply descent_of_endpoint
  · rw [data_20_168831.1]; exact data_20_168831.2.2
  · rw [data_20_168831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 168991). -/
theorem data_20_168991 : oddCount 168991 20 = 12 ∧
    acceleratedOrbit 20 168991 = 85649 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_168991 : ∀ j : Fin 20,
    168991 ≤ acceleratedOrbit j.val 168991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_168991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168991) = 531441 * m + 85649 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 168991
  rw [data_20_168991.1, data_20_168991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_168991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 168991) < 1048576 * m + 168991 := by
  apply descent_of_endpoint
  · rw [data_20_168991.1]; exact data_20_168991.2.2
  · rw [data_20_168991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 169599). -/
theorem data_20_169599 : oddCount 169599 20 = 12 ∧
    acceleratedOrbit 20 169599 = 85957 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_169599 : ∀ j : Fin 20,
    169599 ≤ acceleratedOrbit j.val 169599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_169599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 169599) = 531441 * m + 85957 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 169599
  rw [data_20_169599.1, data_20_169599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_169599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 169599) < 1048576 * m + 169599 := by
  apply descent_of_endpoint
  · rw [data_20_169599.1]; exact data_20_169599.2.2
  · rw [data_20_169599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 169855). -/
theorem data_20_169855 : oddCount 169855 20 = 12 ∧
    acceleratedOrbit 20 169855 = 86087 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_169855 : ∀ j : Fin 20,
    169855 ≤ acceleratedOrbit j.val 169855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_169855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 169855) = 531441 * m + 86087 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 169855
  rw [data_20_169855.1, data_20_169855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_169855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 169855) < 1048576 * m + 169855 := by
  apply descent_of_endpoint
  · rw [data_20_169855.1]; exact data_20_169855.2.2
  · rw [data_20_169855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 170855). -/
theorem data_20_170855 : oddCount 170855 20 = 12 ∧
    acceleratedOrbit 20 170855 = 86594 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_170855 : ∀ j : Fin 20,
    170855 ≤ acceleratedOrbit j.val 170855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_170855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 170855) = 531441 * m + 86594 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 170855
  rw [data_20_170855.1, data_20_170855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_170855 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 170855) < 1048576 * m + 170855 := by
  apply descent_of_endpoint
  · rw [data_20_170855.1]; exact data_20_170855.2.2
  · rw [data_20_170855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 171291). -/
theorem data_20_171291 : oddCount 171291 20 = 12 ∧
    acceleratedOrbit 20 171291 = 86815 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_171291 : ∀ j : Fin 20,
    171291 ≤ acceleratedOrbit j.val 171291 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_171291 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 171291) = 531441 * m + 86815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 171291
  rw [data_20_171291.1, data_20_171291.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_171291 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 171291) < 1048576 * m + 171291 := by
  apply descent_of_endpoint
  · rw [data_20_171291.1]; exact data_20_171291.2.2
  · rw [data_20_171291.2.1]; decide

end Collatz.Research.FirstDescent.Batch275
