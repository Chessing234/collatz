import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 8. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch008
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 207). -/
theorem data_13_207 : oddCount 207 13 = 8 ∧
    acceleratedOrbit 13 207 = 167 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_207 : ∀ j : Fin 13,
    207 ≤ acceleratedOrbit j.val 207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_207 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 207) = 6561 * m + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 207
  rw [data_13_207.1, data_13_207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_207 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 207) < 8192 * m + 207 := by
  apply descent_of_endpoint
  · rw [data_13_207.1]; exact data_13_207.2.2
  · rw [data_13_207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 255). -/
theorem data_13_255 : oddCount 255 13 = 8 ∧
    acceleratedOrbit 13 255 = 205 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_255 : ∀ j : Fin 13,
    255 ≤ acceleratedOrbit j.val 255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_255 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 255) = 6561 * m + 205 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 255
  rw [data_13_255.1, data_13_255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_255 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 255) < 8192 * m + 255 := by
  apply descent_of_endpoint
  · rw [data_13_255.1]; exact data_13_255.2.2
  · rw [data_13_255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 303). -/
theorem data_13_303 : oddCount 303 13 = 8 ∧
    acceleratedOrbit 13 303 = 244 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_303 : ∀ j : Fin 13,
    303 ≤ acceleratedOrbit j.val 303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_303 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 303) = 6561 * m + 244 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 303
  rw [data_13_303.1, data_13_303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_303 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 303) < 8192 * m + 303 := by
  apply descent_of_endpoint
  · rw [data_13_303.1]; exact data_13_303.2.2
  · rw [data_13_303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 539). -/
theorem data_13_539 : oddCount 539 13 = 8 ∧
    acceleratedOrbit 13 539 = 433 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_539 : ∀ j : Fin 13,
    539 ≤ acceleratedOrbit j.val 539 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_539 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 539) = 6561 * m + 433 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 539
  rw [data_13_539.1, data_13_539.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_539 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 539) < 8192 * m + 539 := by
  apply descent_of_endpoint
  · rw [data_13_539.1]; exact data_13_539.2.2
  · rw [data_13_539.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 543). -/
theorem data_13_543 : oddCount 543 13 = 8 ∧
    acceleratedOrbit 13 543 = 436 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_543 : ∀ j : Fin 13,
    543 ≤ acceleratedOrbit j.val 543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_543 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 543) = 6561 * m + 436 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 543
  rw [data_13_543.1, data_13_543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_543 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 543) < 8192 * m + 543 := by
  apply descent_of_endpoint
  · rw [data_13_543.1]; exact data_13_543.2.2
  · rw [data_13_543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 623). -/
theorem data_13_623 : oddCount 623 13 = 8 ∧
    acceleratedOrbit 13 623 = 500 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_623 : ∀ j : Fin 13,
    623 ≤ acceleratedOrbit j.val 623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_623 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 623) = 6561 * m + 500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 623
  rw [data_13_623.1, data_13_623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_623 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 623) < 8192 * m + 623 := by
  apply descent_of_endpoint
  · rw [data_13_623.1]; exact data_13_623.2.2
  · rw [data_13_623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 679). -/
theorem data_13_679 : oddCount 679 13 = 8 ∧
    acceleratedOrbit 13 679 = 545 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_679 : ∀ j : Fin 13,
    679 ≤ acceleratedOrbit j.val 679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_679 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 679) = 6561 * m + 545 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 679
  rw [data_13_679.1, data_13_679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_679 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 679) < 8192 * m + 679 := by
  apply descent_of_endpoint
  · rw [data_13_679.1]; exact data_13_679.2.2
  · rw [data_13_679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 719). -/
theorem data_13_719 : oddCount 719 13 = 8 ∧
    acceleratedOrbit 13 719 = 577 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_719 : ∀ j : Fin 13,
    719 ≤ acceleratedOrbit j.val 719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_719 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 719) = 6561 * m + 577 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 719
  rw [data_13_719.1, data_13_719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_719 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 719) < 8192 * m + 719 := by
  apply descent_of_endpoint
  · rw [data_13_719.1]; exact data_13_719.2.2
  · rw [data_13_719.2.1]; decide

end Collatz.Research.FirstDescent.Batch008
