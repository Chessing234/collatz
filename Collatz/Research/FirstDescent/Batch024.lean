import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 24. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch024
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 8187). -/
theorem data_15_8187 : oddCount 8187 15 = 9 ∧
    acceleratedOrbit 15 8187 = 4919 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_8187 : ∀ j : Fin 15,
    8187 ≤ acceleratedOrbit j.val 8187 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_8187 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8187) = 19683 * m + 4919 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 8187
  rw [data_15_8187.1, data_15_8187.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_8187 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8187) < 32768 * m + 8187 := by
  apply descent_of_endpoint
  · rw [data_15_8187.1]; exact data_15_8187.2.2
  · rw [data_15_8187.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 8347). -/
theorem data_15_8347 : oddCount 8347 15 = 9 ∧
    acceleratedOrbit 15 8347 = 5015 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_8347 : ∀ j : Fin 15,
    8347 ≤ acceleratedOrbit j.val 8347 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_8347 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8347) = 19683 * m + 5015 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 8347
  rw [data_15_8347.1, data_15_8347.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_8347 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8347) < 32768 * m + 8347 := by
  apply descent_of_endpoint
  · rw [data_15_8347.1]; exact data_15_8347.2.2
  · rw [data_15_8347.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 8431). -/
theorem data_15_8431 : oddCount 8431 15 = 9 ∧
    acceleratedOrbit 15 8431 = 5065 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_8431 : ∀ j : Fin 15,
    8431 ≤ acceleratedOrbit j.val 8431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_8431 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8431) = 19683 * m + 5065 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 8431
  rw [data_15_8431.1, data_15_8431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_8431 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8431) < 32768 * m + 8431 := by
  apply descent_of_endpoint
  · rw [data_15_8431.1]; exact data_15_8431.2.2
  · rw [data_15_8431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 8795). -/
theorem data_15_8795 : oddCount 8795 15 = 9 ∧
    acceleratedOrbit 15 8795 = 5284 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_8795 : ∀ j : Fin 15,
    8795 ≤ acceleratedOrbit j.val 8795 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_8795 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8795) = 19683 * m + 5284 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 8795
  rw [data_15_8795.1, data_15_8795.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_8795 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8795) < 32768 * m + 8795 := by
  apply descent_of_endpoint
  · rw [data_15_8795.1]; exact data_15_8795.2.2
  · rw [data_15_8795.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 9051). -/
theorem data_15_9051 : oddCount 9051 15 = 9 ∧
    acceleratedOrbit 15 9051 = 5438 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_9051 : ∀ j : Fin 15,
    9051 ≤ acceleratedOrbit j.val 9051 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_9051 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9051) = 19683 * m + 5438 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 9051
  rw [data_15_9051.1, data_15_9051.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_9051 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9051) < 32768 * m + 9051 := by
  apply descent_of_endpoint
  · rw [data_15_9051.1]; exact data_15_9051.2.2
  · rw [data_15_9051.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 9087). -/
theorem data_15_9087 : oddCount 9087 15 = 9 ∧
    acceleratedOrbit 15 9087 = 5459 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_9087 : ∀ j : Fin 15,
    9087 ≤ acceleratedOrbit j.val 9087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_9087 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9087) = 19683 * m + 5459 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 9087
  rw [data_15_9087.1, data_15_9087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_9087 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9087) < 32768 * m + 9087 := by
  apply descent_of_endpoint
  · rw [data_15_9087.1]; exact data_15_9087.2.2
  · rw [data_15_9087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 9371). -/
theorem data_15_9371 : oddCount 9371 15 = 9 ∧
    acceleratedOrbit 15 9371 = 5630 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_9371 : ∀ j : Fin 15,
    9371 ≤ acceleratedOrbit j.val 9371 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_9371 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9371) = 19683 * m + 5630 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 9371
  rw [data_15_9371.1, data_15_9371.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_9371 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9371) < 32768 * m + 9371 := by
  apply descent_of_endpoint
  · rw [data_15_9371.1]; exact data_15_9371.2.2
  · rw [data_15_9371.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 9375). -/
theorem data_15_9375 : oddCount 9375 15 = 9 ∧
    acceleratedOrbit 15 9375 = 5632 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_9375 : ∀ j : Fin 15,
    9375 ≤ acceleratedOrbit j.val 9375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_9375 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9375) = 19683 * m + 5632 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 9375
  rw [data_15_9375.1, data_15_9375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_9375 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9375) < 32768 * m + 9375 := by
  apply descent_of_endpoint
  · rw [data_15_9375.1]; exact data_15_9375.2.2
  · rw [data_15_9375.2.1]; decide

end Collatz.Research.FirstDescent.Batch024
