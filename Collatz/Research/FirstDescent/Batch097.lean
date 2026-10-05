import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 97. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch097
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 63023). -/
theorem data_16_63023 : oddCount 63023 16 = 10 ∧
    acceleratedOrbit 16 63023 = 56786 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_63023 : ∀ j : Fin 16,
    63023 ≤ acceleratedOrbit j.val 63023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_63023 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63023) = 59049 * m + 56786 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 63023
  rw [data_16_63023.1, data_16_63023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_63023 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63023) < 65536 * m + 63023 := by
  apply descent_of_endpoint
  · rw [data_16_63023.1]; exact data_16_63023.2.2
  · rw [data_16_63023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 63335). -/
theorem data_16_63335 : oddCount 63335 16 = 10 ∧
    acceleratedOrbit 16 63335 = 57067 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_63335 : ∀ j : Fin 16,
    63335 ≤ acceleratedOrbit j.val 63335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_63335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63335) = 59049 * m + 57067 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 63335
  rw [data_16_63335.1, data_16_63335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_63335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63335) < 65536 * m + 63335 := by
  apply descent_of_endpoint
  · rw [data_16_63335.1]; exact data_16_63335.2.2
  · rw [data_16_63335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 63519). -/
theorem data_16_63519 : oddCount 63519 16 = 10 ∧
    acceleratedOrbit 16 63519 = 57233 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_63519 : ∀ j : Fin 16,
    63519 ≤ acceleratedOrbit j.val 63519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_63519 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63519) = 59049 * m + 57233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 63519
  rw [data_16_63519.1, data_16_63519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_63519 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63519) < 65536 * m + 63519 := by
  apply descent_of_endpoint
  · rw [data_16_63519.1]; exact data_16_63519.2.2
  · rw [data_16_63519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 63551). -/
theorem data_16_63551 : oddCount 63551 16 = 10 ∧
    acceleratedOrbit 16 63551 = 57262 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_63551 : ∀ j : Fin 16,
    63551 ≤ acceleratedOrbit j.val 63551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_63551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63551) = 59049 * m + 57262 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 63551
  rw [data_16_63551.1, data_16_63551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_63551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63551) < 65536 * m + 63551 := by
  apply descent_of_endpoint
  · rw [data_16_63551.1]; exact data_16_63551.2.2
  · rw [data_16_63551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 63591). -/
theorem data_16_63591 : oddCount 63591 16 = 10 ∧
    acceleratedOrbit 16 63591 = 57298 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_63591 : ∀ j : Fin 16,
    63591 ≤ acceleratedOrbit j.val 63591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_63591 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63591) = 59049 * m + 57298 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 63591
  rw [data_16_63591.1, data_16_63591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_63591 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63591) < 65536 * m + 63591 := by
  apply descent_of_endpoint
  · rw [data_16_63591.1]; exact data_16_63591.2.2
  · rw [data_16_63591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 63599). -/
theorem data_16_63599 : oddCount 63599 16 = 10 ∧
    acceleratedOrbit 16 63599 = 57305 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_63599 : ∀ j : Fin 16,
    63599 ≤ acceleratedOrbit j.val 63599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_63599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63599) = 59049 * m + 57305 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 63599
  rw [data_16_63599.1, data_16_63599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_63599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 63599) < 65536 * m + 63599 := by
  apply descent_of_endpoint
  · rw [data_16_63599.1]; exact data_16_63599.2.2
  · rw [data_16_63599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64047). -/
theorem data_16_64047 : oddCount 64047 16 = 10 ∧
    acceleratedOrbit 16 64047 = 57709 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64047 : ∀ j : Fin 16,
    64047 ≤ acceleratedOrbit j.val 64047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64047 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64047) = 59049 * m + 57709 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64047
  rw [data_16_64047.1, data_16_64047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64047 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64047) < 65536 * m + 64047 := by
  apply descent_of_endpoint
  · rw [data_16_64047.1]; exact data_16_64047.2.2
  · rw [data_16_64047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 64167). -/
theorem data_16_64167 : oddCount 64167 16 = 10 ∧
    acceleratedOrbit 16 64167 = 57817 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_64167 : ∀ j : Fin 16,
    64167 ≤ acceleratedOrbit j.val 64167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_64167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64167) = 59049 * m + 57817 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 64167
  rw [data_16_64167.1, data_16_64167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_64167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 64167) < 65536 * m + 64167 := by
  apply descent_of_endpoint
  · rw [data_16_64167.1]; exact data_16_64167.2.2
  · rw [data_16_64167.2.1]; decide

end Collatz.Research.FirstDescent.Batch097
