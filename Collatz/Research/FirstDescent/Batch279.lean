import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 279. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch279
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 181759). -/
theorem data_20_181759 : oddCount 181759 20 = 12 ∧
    acceleratedOrbit 20 181759 = 92120 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_181759 : ∀ j : Fin 20,
    181759 ≤ acceleratedOrbit j.val 181759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_181759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181759) = 531441 * m + 92120 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 181759
  rw [data_20_181759.1, data_20_181759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_181759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181759) < 1048576 * m + 181759 := by
  apply descent_of_endpoint
  · rw [data_20_181759.1]; exact data_20_181759.2.2
  · rw [data_20_181759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 181999). -/
theorem data_20_181999 : oddCount 181999 20 = 12 ∧
    acceleratedOrbit 20 181999 = 92242 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_181999 : ∀ j : Fin 20,
    181999 ≤ acceleratedOrbit j.val 181999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_181999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181999) = 531441 * m + 92242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 181999
  rw [data_20_181999.1, data_20_181999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_181999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181999) < 1048576 * m + 181999 := by
  apply descent_of_endpoint
  · rw [data_20_181999.1]; exact data_20_181999.2.2
  · rw [data_20_181999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 182107). -/
theorem data_20_182107 : oddCount 182107 20 = 12 ∧
    acceleratedOrbit 20 182107 = 92297 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_182107 : ∀ j : Fin 20,
    182107 ≤ acceleratedOrbit j.val 182107 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_182107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 182107) = 531441 * m + 92297 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 182107
  rw [data_20_182107.1, data_20_182107.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_182107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 182107) < 1048576 * m + 182107 := by
  apply descent_of_endpoint
  · rw [data_20_182107.1]; exact data_20_182107.2.2
  · rw [data_20_182107.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 182599). -/
theorem data_20_182599 : oddCount 182599 20 = 12 ∧
    acceleratedOrbit 20 182599 = 92546 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_182599 : ∀ j : Fin 20,
    182599 ≤ acceleratedOrbit j.val 182599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_182599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 182599) = 531441 * m + 92546 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 182599
  rw [data_20_182599.1, data_20_182599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_182599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 182599) < 1048576 * m + 182599 := by
  apply descent_of_endpoint
  · rw [data_20_182599.1]; exact data_20_182599.2.2
  · rw [data_20_182599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 182895). -/
theorem data_20_182895 : oddCount 182895 20 = 12 ∧
    acceleratedOrbit 20 182895 = 92696 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_182895 : ∀ j : Fin 20,
    182895 ≤ acceleratedOrbit j.val 182895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_182895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 182895) = 531441 * m + 92696 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 182895
  rw [data_20_182895.1, data_20_182895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_182895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 182895) < 1048576 * m + 182895 := by
  apply descent_of_endpoint
  · rw [data_20_182895.1]; exact data_20_182895.2.2
  · rw [data_20_182895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 183599). -/
theorem data_20_183599 : oddCount 183599 20 = 12 ∧
    acceleratedOrbit 20 183599 = 93053 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_183599 : ∀ j : Fin 20,
    183599 ≤ acceleratedOrbit j.val 183599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_183599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 183599) = 531441 * m + 93053 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 183599
  rw [data_20_183599.1, data_20_183599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_183599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 183599) < 1048576 * m + 183599 := by
  apply descent_of_endpoint
  · rw [data_20_183599.1]; exact data_20_183599.2.2
  · rw [data_20_183599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 184351). -/
theorem data_20_184351 : oddCount 184351 20 = 12 ∧
    acceleratedOrbit 20 184351 = 93434 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_184351 : ∀ j : Fin 20,
    184351 ≤ acceleratedOrbit j.val 184351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_184351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 184351) = 531441 * m + 93434 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 184351
  rw [data_20_184351.1, data_20_184351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_184351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 184351) < 1048576 * m + 184351 := by
  apply descent_of_endpoint
  · rw [data_20_184351.1]; exact data_20_184351.2.2
  · rw [data_20_184351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 184831). -/
theorem data_20_184831 : oddCount 184831 20 = 12 ∧
    acceleratedOrbit 20 184831 = 93677 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_184831 : ∀ j : Fin 20,
    184831 ≤ acceleratedOrbit j.val 184831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_184831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 184831) = 531441 * m + 93677 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 184831
  rw [data_20_184831.1, data_20_184831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_184831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 184831) < 1048576 * m + 184831 := by
  apply descent_of_endpoint
  · rw [data_20_184831.1]; exact data_20_184831.2.2
  · rw [data_20_184831.2.1]; decide

end Collatz.Research.FirstDescent.Batch279
