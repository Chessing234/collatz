import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 58. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch058
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19707). -/
theorem data_16_19707 : oddCount 19707 16 = 10 ∧
    acceleratedOrbit 16 19707 = 17758 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19707 : ∀ j : Fin 16,
    19707 ≤ acceleratedOrbit j.val 19707 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19707 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19707) = 59049 * m + 17758 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19707
  rw [data_16_19707.1, data_16_19707.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19707 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19707) < 65536 * m + 19707 := by
  apply descent_of_endpoint
  · rw [data_16_19707.1]; exact data_16_19707.2.2
  · rw [data_16_19707.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 20127). -/
theorem data_16_20127 : oddCount 20127 16 = 10 ∧
    acceleratedOrbit 16 20127 = 18136 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_20127 : ∀ j : Fin 16,
    20127 ≤ acceleratedOrbit j.val 20127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_20127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20127) = 59049 * m + 18136 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 20127
  rw [data_16_20127.1, data_16_20127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_20127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20127) < 65536 * m + 20127 := by
  apply descent_of_endpoint
  · rw [data_16_20127.1]; exact data_16_20127.2.2
  · rw [data_16_20127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 20207). -/
theorem data_16_20207 : oddCount 20207 16 = 10 ∧
    acceleratedOrbit 16 20207 = 18208 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_20207 : ∀ j : Fin 16,
    20207 ≤ acceleratedOrbit j.val 20207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_20207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20207) = 59049 * m + 18208 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 20207
  rw [data_16_20207.1, data_16_20207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_20207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20207) < 65536 * m + 20207 := by
  apply descent_of_endpoint
  · rw [data_16_20207.1]; exact data_16_20207.2.2
  · rw [data_16_20207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 20511). -/
theorem data_16_20511 : oddCount 20511 16 = 10 ∧
    acceleratedOrbit 16 20511 = 18482 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_20511 : ∀ j : Fin 16,
    20511 ≤ acceleratedOrbit j.val 20511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_20511 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20511) = 59049 * m + 18482 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 20511
  rw [data_16_20511.1, data_16_20511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_20511 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20511) < 65536 * m + 20511 := by
  apply descent_of_endpoint
  · rw [data_16_20511.1]; exact data_16_20511.2.2
  · rw [data_16_20511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 20591). -/
theorem data_16_20591 : oddCount 20591 16 = 10 ∧
    acceleratedOrbit 16 20591 = 18554 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_20591 : ∀ j : Fin 16,
    20591 ≤ acceleratedOrbit j.val 20591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_20591 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20591) = 59049 * m + 18554 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 20591
  rw [data_16_20591.1, data_16_20591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_20591 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20591) < 65536 * m + 20591 := by
  apply descent_of_endpoint
  · rw [data_16_20591.1]; exact data_16_20591.2.2
  · rw [data_16_20591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 20687). -/
theorem data_16_20687 : oddCount 20687 16 = 10 ∧
    acceleratedOrbit 16 20687 = 18641 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_20687 : ∀ j : Fin 16,
    20687 ≤ acceleratedOrbit j.val 20687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_20687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20687) = 59049 * m + 18641 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 20687
  rw [data_16_20687.1, data_16_20687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_20687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20687) < 65536 * m + 20687 := by
  apply descent_of_endpoint
  · rw [data_16_20687.1]; exact data_16_20687.2.2
  · rw [data_16_20687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 20807). -/
theorem data_16_20807 : oddCount 20807 16 = 10 ∧
    acceleratedOrbit 16 20807 = 18749 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_20807 : ∀ j : Fin 16,
    20807 ≤ acceleratedOrbit j.val 20807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_20807 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20807) = 59049 * m + 18749 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 20807
  rw [data_16_20807.1, data_16_20807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_20807 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 20807) < 65536 * m + 20807 := by
  apply descent_of_endpoint
  · rw [data_16_20807.1]; exact data_16_20807.2.2
  · rw [data_16_20807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 21039). -/
theorem data_16_21039 : oddCount 21039 16 = 10 ∧
    acceleratedOrbit 16 21039 = 18958 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_21039 : ∀ j : Fin 16,
    21039 ≤ acceleratedOrbit j.val 21039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_21039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21039) = 59049 * m + 18958 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 21039
  rw [data_16_21039.1, data_16_21039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_21039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21039) < 65536 * m + 21039 := by
  apply descent_of_endpoint
  · rw [data_16_21039.1]; exact data_16_21039.2.2
  · rw [data_16_21039.2.1]; decide

end Collatz.Research.FirstDescent.Batch058
