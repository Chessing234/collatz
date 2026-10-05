import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 12. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch012
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3483). -/
theorem data_13_3483 : oddCount 3483 13 = 8 ∧
    acceleratedOrbit 13 3483 = 2791 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3483 : ∀ j : Fin 13,
    3483 ≤ acceleratedOrbit j.val 3483 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3483 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3483) = 6561 * m + 2791 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3483
  rw [data_13_3483.1, data_13_3483.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3483 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3483) < 8192 * m + 3483 := by
  apply descent_of_endpoint
  · rw [data_13_3483.1]; exact data_13_3483.2.2
  · rw [data_13_3483.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3551). -/
theorem data_13_3551 : oddCount 3551 13 = 8 ∧
    acceleratedOrbit 13 3551 = 2845 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3551 : ∀ j : Fin 13,
    3551 ≤ acceleratedOrbit j.val 3551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3551 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3551) = 6561 * m + 2845 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3551
  rw [data_13_3551.1, data_13_3551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3551 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3551) < 8192 * m + 3551 := by
  apply descent_of_endpoint
  · rw [data_13_3551.1]; exact data_13_3551.2.2
  · rw [data_13_3551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3687). -/
theorem data_13_3687 : oddCount 3687 13 = 8 ∧
    acceleratedOrbit 13 3687 = 2954 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3687 : ∀ j : Fin 13,
    3687 ≤ acceleratedOrbit j.val 3687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3687 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3687) = 6561 * m + 2954 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3687
  rw [data_13_3687.1, data_13_3687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3687 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3687) < 8192 * m + 3687 := by
  apply descent_of_endpoint
  · rw [data_13_3687.1]; exact data_13_3687.2.2
  · rw [data_13_3687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3835). -/
theorem data_13_3835 : oddCount 3835 13 = 8 ∧
    acceleratedOrbit 13 3835 = 3073 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3835 : ∀ j : Fin 13,
    3835 ≤ acceleratedOrbit j.val 3835 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3835 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3835) = 6561 * m + 3073 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3835
  rw [data_13_3835.1, data_13_3835.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3835 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3835) < 8192 * m + 3835 := by
  apply descent_of_endpoint
  · rw [data_13_3835.1]; exact data_13_3835.2.2
  · rw [data_13_3835.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3903). -/
theorem data_13_3903 : oddCount 3903 13 = 8 ∧
    acceleratedOrbit 13 3903 = 3127 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3903 : ∀ j : Fin 13,
    3903 ≤ acceleratedOrbit j.val 3903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3903 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3903) = 6561 * m + 3127 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3903
  rw [data_13_3903.1, data_13_3903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3903 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3903) < 8192 * m + 3903 := by
  apply descent_of_endpoint
  · rw [data_13_3903.1]; exact data_13_3903.2.2
  · rw [data_13_3903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3967). -/
theorem data_13_3967 : oddCount 3967 13 = 8 ∧
    acceleratedOrbit 13 3967 = 3178 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3967 : ∀ j : Fin 13,
    3967 ≤ acceleratedOrbit j.val 3967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3967 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3967) = 6561 * m + 3178 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3967
  rw [data_13_3967.1, data_13_3967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3967 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3967) < 8192 * m + 3967 := by
  apply descent_of_endpoint
  · rw [data_13_3967.1]; exact data_13_3967.2.2
  · rw [data_13_3967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4079). -/
theorem data_13_4079 : oddCount 4079 13 = 8 ∧
    acceleratedOrbit 13 4079 = 3268 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4079 : ∀ j : Fin 13,
    4079 ≤ acceleratedOrbit j.val 4079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4079 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4079) = 6561 * m + 3268 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4079
  rw [data_13_4079.1, data_13_4079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4079 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4079) < 8192 * m + 4079 := by
  apply descent_of_endpoint
  · rw [data_13_4079.1]; exact data_13_4079.2.2
  · rw [data_13_4079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4091). -/
theorem data_13_4091 : oddCount 4091 13 = 8 ∧
    acceleratedOrbit 13 4091 = 3278 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4091 : ∀ j : Fin 13,
    4091 ≤ acceleratedOrbit j.val 4091 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4091 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4091) = 6561 * m + 3278 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4091
  rw [data_13_4091.1, data_13_4091.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4091 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4091) < 8192 * m + 4091 := by
  apply descent_of_endpoint
  · rw [data_13_4091.1]; exact data_13_4091.2.2
  · rw [data_13_4091.2.1]; decide

end Collatz.Research.FirstDescent.Batch012
