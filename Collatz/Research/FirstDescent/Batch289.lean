import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 289. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch289
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 205563). -/
theorem data_20_205563 : oddCount 205563 20 = 12 ∧
    acceleratedOrbit 20 205563 = 104185 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_205563 : ∀ j : Fin 20,
    205563 ≤ acceleratedOrbit j.val 205563 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_205563 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 205563) = 531441 * m + 104185 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 205563
  rw [data_20_205563.1, data_20_205563.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_205563 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 205563) < 1048576 * m + 205563 := by
  apply descent_of_endpoint
  · rw [data_20_205563.1]; exact data_20_205563.2.2
  · rw [data_20_205563.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 206079). -/
theorem data_20_206079 : oddCount 206079 20 = 12 ∧
    acceleratedOrbit 20 206079 = 104446 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_206079 : ∀ j : Fin 20,
    206079 ≤ acceleratedOrbit j.val 206079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_206079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 206079) = 531441 * m + 104446 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 206079
  rw [data_20_206079.1, data_20_206079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_206079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 206079) < 1048576 * m + 206079 := by
  apply descent_of_endpoint
  · rw [data_20_206079.1]; exact data_20_206079.2.2
  · rw [data_20_206079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 207055). -/
theorem data_20_207055 : oddCount 207055 20 = 12 ∧
    acceleratedOrbit 20 207055 = 104941 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_207055 : ∀ j : Fin 20,
    207055 ≤ acceleratedOrbit j.val 207055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_207055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207055) = 531441 * m + 104941 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 207055
  rw [data_20_207055.1, data_20_207055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_207055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207055) < 1048576 * m + 207055 := by
  apply descent_of_endpoint
  · rw [data_20_207055.1]; exact data_20_207055.2.2
  · rw [data_20_207055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 207103). -/
theorem data_20_207103 : oddCount 207103 20 = 12 ∧
    acceleratedOrbit 20 207103 = 104965 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_207103 : ∀ j : Fin 20,
    207103 ≤ acceleratedOrbit j.val 207103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_207103 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207103) = 531441 * m + 104965 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 207103
  rw [data_20_207103.1, data_20_207103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_207103 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207103) < 1048576 * m + 207103 := by
  apply descent_of_endpoint
  · rw [data_20_207103.1]; exact data_20_207103.2.2
  · rw [data_20_207103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 207311). -/
theorem data_20_207311 : oddCount 207311 20 = 12 ∧
    acceleratedOrbit 20 207311 = 105071 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_207311 : ∀ j : Fin 20,
    207311 ≤ acceleratedOrbit j.val 207311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_207311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207311) = 531441 * m + 105071 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 207311
  rw [data_20_207311.1, data_20_207311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_207311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207311) < 1048576 * m + 207311 := by
  apply descent_of_endpoint
  · rw [data_20_207311.1]; exact data_20_207311.2.2
  · rw [data_20_207311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 207519). -/
theorem data_20_207519 : oddCount 207519 20 = 12 ∧
    acceleratedOrbit 20 207519 = 105176 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_207519 : ∀ j : Fin 20,
    207519 ≤ acceleratedOrbit j.val 207519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_207519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207519) = 531441 * m + 105176 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 207519
  rw [data_20_207519.1, data_20_207519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_207519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 207519) < 1048576 * m + 207519 := by
  apply descent_of_endpoint
  · rw [data_20_207519.1]; exact data_20_207519.2.2
  · rw [data_20_207519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 208199). -/
theorem data_20_208199 : oddCount 208199 20 = 12 ∧
    acceleratedOrbit 20 208199 = 105521 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_208199 : ∀ j : Fin 20,
    208199 ≤ acceleratedOrbit j.val 208199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_208199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 208199) = 531441 * m + 105521 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 208199
  rw [data_20_208199.1, data_20_208199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_208199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 208199) < 1048576 * m + 208199 := by
  apply descent_of_endpoint
  · rw [data_20_208199.1]; exact data_20_208199.2.2
  · rw [data_20_208199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 208807). -/
theorem data_20_208807 : oddCount 208807 20 = 12 ∧
    acceleratedOrbit 20 208807 = 105829 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_208807 : ∀ j : Fin 20,
    208807 ≤ acceleratedOrbit j.val 208807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_208807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 208807) = 531441 * m + 105829 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 208807
  rw [data_20_208807.1, data_20_208807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_208807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 208807) < 1048576 * m + 208807 := by
  apply descent_of_endpoint
  · rw [data_20_208807.1]; exact data_20_208807.2.2
  · rw [data_20_208807.2.1]; decide

end Collatz.Research.FirstDescent.Batch289
