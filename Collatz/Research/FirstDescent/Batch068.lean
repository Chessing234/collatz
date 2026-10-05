import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 68. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch068
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30971). -/
theorem data_16_30971 : oddCount 30971 16 = 10 ∧
    acceleratedOrbit 16 30971 = 27907 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30971 : ∀ j : Fin 16,
    30971 ≤ acceleratedOrbit j.val 30971 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30971 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30971) = 59049 * m + 27907 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30971
  rw [data_16_30971.1, data_16_30971.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30971 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30971) < 65536 * m + 30971 := by
  apply descent_of_endpoint
  · rw [data_16_30971.1]; exact data_16_30971.2.2
  · rw [data_16_30971.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 30975). -/
theorem data_16_30975 : oddCount 30975 16 = 10 ∧
    acceleratedOrbit 16 30975 = 27910 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_30975 : ∀ j : Fin 16,
    30975 ≤ acceleratedOrbit j.val 30975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_30975 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30975) = 59049 * m + 27910 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 30975
  rw [data_16_30975.1, data_16_30975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_30975 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 30975) < 65536 * m + 30975 := by
  apply descent_of_endpoint
  · rw [data_16_30975.1]; exact data_16_30975.2.2
  · rw [data_16_30975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 31079). -/
theorem data_16_31079 : oddCount 31079 16 = 10 ∧
    acceleratedOrbit 16 31079 = 28004 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_31079 : ∀ j : Fin 16,
    31079 ≤ acceleratedOrbit j.val 31079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_31079 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31079) = 59049 * m + 28004 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 31079
  rw [data_16_31079.1, data_16_31079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_31079 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31079) < 65536 * m + 31079 := by
  apply descent_of_endpoint
  · rw [data_16_31079.1]; exact data_16_31079.2.2
  · rw [data_16_31079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 31199). -/
theorem data_16_31199 : oddCount 31199 16 = 10 ∧
    acceleratedOrbit 16 31199 = 28112 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_31199 : ∀ j : Fin 16,
    31199 ≤ acceleratedOrbit j.val 31199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_31199 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31199) = 59049 * m + 28112 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 31199
  rw [data_16_31199.1, data_16_31199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_31199 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31199) < 65536 * m + 31199 := by
  apply descent_of_endpoint
  · rw [data_16_31199.1]; exact data_16_31199.2.2
  · rw [data_16_31199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 31335). -/
theorem data_16_31335 : oddCount 31335 16 = 10 ∧
    acceleratedOrbit 16 31335 = 28235 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_31335 : ∀ j : Fin 16,
    31335 ≤ acceleratedOrbit j.val 31335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_31335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31335) = 59049 * m + 28235 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 31335
  rw [data_16_31335.1, data_16_31335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_31335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31335) < 65536 * m + 31335 := by
  apply descent_of_endpoint
  · rw [data_16_31335.1]; exact data_16_31335.2.2
  · rw [data_16_31335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 31359). -/
theorem data_16_31359 : oddCount 31359 16 = 10 ∧
    acceleratedOrbit 16 31359 = 28256 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_31359 : ∀ j : Fin 16,
    31359 ≤ acceleratedOrbit j.val 31359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_31359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31359) = 59049 * m + 28256 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 31359
  rw [data_16_31359.1, data_16_31359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_31359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31359) < 65536 * m + 31359 := by
  apply descent_of_endpoint
  · rw [data_16_31359.1]; exact data_16_31359.2.2
  · rw [data_16_31359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 31471). -/
theorem data_16_31471 : oddCount 31471 16 = 10 ∧
    acceleratedOrbit 16 31471 = 28357 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_31471 : ∀ j : Fin 16,
    31471 ≤ acceleratedOrbit j.val 31471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_31471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31471) = 59049 * m + 28357 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 31471
  rw [data_16_31471.1, data_16_31471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_31471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31471) < 65536 * m + 31471 := by
  apply descent_of_endpoint
  · rw [data_16_31471.1]; exact data_16_31471.2.2
  · rw [data_16_31471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 31727). -/
theorem data_16_31727 : oddCount 31727 16 = 10 ∧
    acceleratedOrbit 16 31727 = 28588 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_31727 : ∀ j : Fin 16,
    31727 ≤ acceleratedOrbit j.val 31727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_31727 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31727) = 59049 * m + 28588 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 31727
  rw [data_16_31727.1, data_16_31727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_31727 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 31727) < 65536 * m + 31727 := by
  apply descent_of_endpoint
  · rw [data_16_31727.1]; exact data_16_31727.2.2
  · rw [data_16_31727.2.1]; decide

end Collatz.Research.FirstDescent.Batch068
