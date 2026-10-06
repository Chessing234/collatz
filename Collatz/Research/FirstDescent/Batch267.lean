import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 267. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch267
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 141567). -/
theorem data_20_141567 : oddCount 141567 20 = 12 ∧
    acceleratedOrbit 20 141567 = 71750 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_141567 : ∀ j : Fin 20,
    141567 ≤ acceleratedOrbit j.val 141567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_141567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 141567) = 531441 * m + 71750 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 141567
  rw [data_20_141567.1, data_20_141567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_141567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 141567) < 1048576 * m + 141567 := by
  apply descent_of_endpoint
  · rw [data_20_141567.1]; exact data_20_141567.2.2
  · rw [data_20_141567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 142247). -/
theorem data_20_142247 : oddCount 142247 20 = 12 ∧
    acceleratedOrbit 20 142247 = 72095 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_142247 : ∀ j : Fin 20,
    142247 ≤ acceleratedOrbit j.val 142247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_142247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 142247) = 531441 * m + 72095 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 142247
  rw [data_20_142247.1, data_20_142247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_142247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 142247) < 1048576 * m + 142247 := by
  apply descent_of_endpoint
  · rw [data_20_142247.1]; exact data_20_142247.2.2
  · rw [data_20_142247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 142567). -/
theorem data_20_142567 : oddCount 142567 20 = 12 ∧
    acceleratedOrbit 20 142567 = 72257 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_142567 : ∀ j : Fin 20,
    142567 ≤ acceleratedOrbit j.val 142567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_142567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 142567) = 531441 * m + 72257 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 142567
  rw [data_20_142567.1, data_20_142567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_142567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 142567) < 1048576 * m + 142567 := by
  apply descent_of_endpoint
  · rw [data_20_142567.1]; exact data_20_142567.2.2
  · rw [data_20_142567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 143003). -/
theorem data_20_143003 : oddCount 143003 20 = 12 ∧
    acceleratedOrbit 20 143003 = 72478 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_143003 : ∀ j : Fin 20,
    143003 ≤ acceleratedOrbit j.val 143003 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_143003 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 143003) = 531441 * m + 72478 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 143003
  rw [data_20_143003.1, data_20_143003.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_143003 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 143003) < 1048576 * m + 143003 := by
  apply descent_of_endpoint
  · rw [data_20_143003.1]; exact data_20_143003.2.2
  · rw [data_20_143003.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 143271). -/
theorem data_20_143271 : oddCount 143271 20 = 12 ∧
    acceleratedOrbit 20 143271 = 72614 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_143271 : ∀ j : Fin 20,
    143271 ≤ acceleratedOrbit j.val 143271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_143271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 143271) = 531441 * m + 72614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 143271
  rw [data_20_143271.1, data_20_143271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_143271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 143271) < 1048576 * m + 143271 := by
  apply descent_of_endpoint
  · rw [data_20_143271.1]; exact data_20_143271.2.2
  · rw [data_20_143271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 143775). -/
theorem data_20_143775 : oddCount 143775 20 = 12 ∧
    acceleratedOrbit 20 143775 = 72869 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_143775 : ∀ j : Fin 20,
    143775 ≤ acceleratedOrbit j.val 143775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_143775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 143775) = 531441 * m + 72869 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 143775
  rw [data_20_143775.1, data_20_143775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_143775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 143775) < 1048576 * m + 143775 := by
  apply descent_of_endpoint
  · rw [data_20_143775.1]; exact data_20_143775.2.2
  · rw [data_20_143775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 144383). -/
theorem data_20_144383 : oddCount 144383 20 = 12 ∧
    acceleratedOrbit 20 144383 = 73177 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_144383 : ∀ j : Fin 20,
    144383 ≤ acceleratedOrbit j.val 144383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_144383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 144383) = 531441 * m + 73177 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 144383
  rw [data_20_144383.1, data_20_144383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_144383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 144383) < 1048576 * m + 144383 := by
  apply descent_of_endpoint
  · rw [data_20_144383.1]; exact data_20_144383.2.2
  · rw [data_20_144383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 144431). -/
theorem data_20_144431 : oddCount 144431 20 = 12 ∧
    acceleratedOrbit 20 144431 = 73202 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_144431 : ∀ j : Fin 20,
    144431 ≤ acceleratedOrbit j.val 144431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_144431 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 144431) = 531441 * m + 73202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 144431
  rw [data_20_144431.1, data_20_144431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_144431 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 144431) < 1048576 * m + 144431 := by
  apply descent_of_endpoint
  · rw [data_20_144431.1]; exact data_20_144431.2.2
  · rw [data_20_144431.2.1]; decide

end Collatz.Research.FirstDescent.Batch267
