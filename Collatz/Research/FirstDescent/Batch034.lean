import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 34. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch034
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 22939). -/
theorem data_15_22939 : oddCount 22939 15 = 9 ∧
    acceleratedOrbit 15 22939 = 13780 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_22939 : ∀ j : Fin 15,
    22939 ≤ acceleratedOrbit j.val 22939 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_22939 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22939) = 19683 * m + 13780 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 22939
  rw [data_15_22939.1, data_15_22939.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_22939 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22939) < 32768 * m + 22939 := by
  apply descent_of_endpoint
  · rw [data_15_22939.1]; exact data_15_22939.2.2
  · rw [data_15_22939.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 23231). -/
theorem data_15_23231 : oddCount 23231 15 = 9 ∧
    acceleratedOrbit 15 23231 = 13955 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_23231 : ∀ j : Fin 15,
    23231 ≤ acceleratedOrbit j.val 23231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_23231 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23231) = 19683 * m + 13955 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 23231
  rw [data_15_23231.1, data_15_23231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_23231 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23231) < 32768 * m + 23231 := by
  apply descent_of_endpoint
  · rw [data_15_23231.1]; exact data_15_23231.2.2
  · rw [data_15_23231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 23359). -/
theorem data_15_23359 : oddCount 23359 15 = 9 ∧
    acceleratedOrbit 15 23359 = 14032 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_23359 : ∀ j : Fin 15,
    23359 ≤ acceleratedOrbit j.val 23359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_23359 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23359) = 19683 * m + 14032 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 23359
  rw [data_15_23359.1, data_15_23359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_23359 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23359) < 32768 * m + 23359 := by
  apply descent_of_endpoint
  · rw [data_15_23359.1]; exact data_15_23359.2.2
  · rw [data_15_23359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 23399). -/
theorem data_15_23399 : oddCount 23399 15 = 9 ∧
    acceleratedOrbit 15 23399 = 14056 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_23399 : ∀ j : Fin 15,
    23399 ≤ acceleratedOrbit j.val 23399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_23399 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23399) = 19683 * m + 14056 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 23399
  rw [data_15_23399.1, data_15_23399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_23399 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23399) < 32768 * m + 23399 := by
  apply descent_of_endpoint
  · rw [data_15_23399.1]; exact data_15_23399.2.2
  · rw [data_15_23399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 23615). -/
theorem data_15_23615 : oddCount 23615 15 = 9 ∧
    acceleratedOrbit 15 23615 = 14186 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_23615 : ∀ j : Fin 15,
    23615 ≤ acceleratedOrbit j.val 23615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_23615 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23615) = 19683 * m + 14186 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 23615
  rw [data_15_23615.1, data_15_23615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_23615 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23615) < 32768 * m + 23615 := by
  apply descent_of_endpoint
  · rw [data_15_23615.1]; exact data_15_23615.2.2
  · rw [data_15_23615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 23803). -/
theorem data_15_23803 : oddCount 23803 15 = 9 ∧
    acceleratedOrbit 15 23803 = 14299 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_23803 : ∀ j : Fin 15,
    23803 ≤ acceleratedOrbit j.val 23803 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_23803 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23803) = 19683 * m + 14299 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 23803
  rw [data_15_23803.1, data_15_23803.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_23803 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23803) < 32768 * m + 23803 := by
  apply descent_of_endpoint
  · rw [data_15_23803.1]; exact data_15_23803.2.2
  · rw [data_15_23803.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 23835). -/
theorem data_15_23835 : oddCount 23835 15 = 9 ∧
    acceleratedOrbit 15 23835 = 14318 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_23835 : ∀ j : Fin 15,
    23835 ≤ acceleratedOrbit j.val 23835 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_23835 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23835) = 19683 * m + 14318 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 23835
  rw [data_15_23835.1, data_15_23835.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_23835 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23835) < 32768 * m + 23835 := by
  apply descent_of_endpoint
  · rw [data_15_23835.1]; exact data_15_23835.2.2
  · rw [data_15_23835.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 23935). -/
theorem data_15_23935 : oddCount 23935 15 = 9 ∧
    acceleratedOrbit 15 23935 = 14378 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_23935 : ∀ j : Fin 15,
    23935 ≤ acceleratedOrbit j.val 23935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_23935 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23935) = 19683 * m + 14378 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 23935
  rw [data_15_23935.1, data_15_23935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_23935 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 23935) < 32768 * m + 23935 := by
  apply descent_of_endpoint
  · rw [data_15_23935.1]; exact data_15_23935.2.2
  · rw [data_15_23935.2.1]; decide

end Collatz.Research.FirstDescent.Batch034
