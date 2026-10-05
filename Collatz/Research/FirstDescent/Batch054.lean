import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 54. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch054
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15743). -/
theorem data_16_15743 : oddCount 15743 16 = 10 ∧
    acceleratedOrbit 16 15743 = 14186 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15743 : ∀ j : Fin 16,
    15743 ≤ acceleratedOrbit j.val 15743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15743 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15743) = 59049 * m + 14186 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15743
  rw [data_16_15743.1, data_16_15743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15743 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15743) < 65536 * m + 15743 := by
  apply descent_of_endpoint
  · rw [data_16_15743.1]; exact data_16_15743.2.2
  · rw [data_16_15743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15771). -/
theorem data_16_15771 : oddCount 15771 16 = 10 ∧
    acceleratedOrbit 16 15771 = 14212 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15771 : ∀ j : Fin 16,
    15771 ≤ acceleratedOrbit j.val 15771 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15771 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15771) = 59049 * m + 14212 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15771
  rw [data_16_15771.1, data_16_15771.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15771 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15771) < 65536 * m + 15771 := by
  apply descent_of_endpoint
  · rw [data_16_15771.1]; exact data_16_15771.2.2
  · rw [data_16_15771.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15855). -/
theorem data_16_15855 : oddCount 15855 16 = 10 ∧
    acceleratedOrbit 16 15855 = 14287 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15855 : ∀ j : Fin 16,
    15855 ≤ acceleratedOrbit j.val 15855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15855 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15855) = 59049 * m + 14287 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15855
  rw [data_16_15855.1, data_16_15855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15855 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15855) < 65536 * m + 15855 := by
  apply descent_of_endpoint
  · rw [data_16_15855.1]; exact data_16_15855.2.2
  · rw [data_16_15855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 16191). -/
theorem data_16_16191 : oddCount 16191 16 = 10 ∧
    acceleratedOrbit 16 16191 = 14590 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_16191 : ∀ j : Fin 16,
    16191 ≤ acceleratedOrbit j.val 16191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_16191 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16191) = 59049 * m + 14590 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 16191
  rw [data_16_16191.1, data_16_16191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_16191 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16191) < 65536 * m + 16191 := by
  apply descent_of_endpoint
  · rw [data_16_16191.1]; exact data_16_16191.2.2
  · rw [data_16_16191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 16411). -/
theorem data_16_16411 : oddCount 16411 16 = 10 ∧
    acceleratedOrbit 16 16411 = 14788 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_16411 : ∀ j : Fin 16,
    16411 ≤ acceleratedOrbit j.val 16411 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_16411 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16411) = 59049 * m + 14788 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 16411
  rw [data_16_16411.1, data_16_16411.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_16411 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16411) < 65536 * m + 16411 := by
  apply descent_of_endpoint
  · rw [data_16_16411.1]; exact data_16_16411.2.2
  · rw [data_16_16411.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 16431). -/
theorem data_16_16431 : oddCount 16431 16 = 10 ∧
    acceleratedOrbit 16 16431 = 14806 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_16431 : ∀ j : Fin 16,
    16431 ≤ acceleratedOrbit j.val 16431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_16431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16431) = 59049 * m + 14806 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 16431
  rw [data_16_16431.1, data_16_16431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_16431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16431) < 65536 * m + 16431 := by
  apply descent_of_endpoint
  · rw [data_16_16431.1]; exact data_16_16431.2.2
  · rw [data_16_16431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 16455). -/
theorem data_16_16455 : oddCount 16455 16 = 10 ∧
    acceleratedOrbit 16 16455 = 14828 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_16455 : ∀ j : Fin 16,
    16455 ≤ acceleratedOrbit j.val 16455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_16455 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16455) = 59049 * m + 14828 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 16455
  rw [data_16_16455.1, data_16_16455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_16455 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16455) < 65536 * m + 16455 := by
  apply descent_of_endpoint
  · rw [data_16_16455.1]; exact data_16_16455.2.2
  · rw [data_16_16455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 16511). -/
theorem data_16_16511 : oddCount 16511 16 = 10 ∧
    acceleratedOrbit 16 16511 = 14878 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_16511 : ∀ j : Fin 16,
    16511 ≤ acceleratedOrbit j.val 16511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_16511 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16511) = 59049 * m + 14878 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 16511
  rw [data_16_16511.1, data_16_16511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_16511 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16511) < 65536 * m + 16511 := by
  apply descent_of_endpoint
  · rw [data_16_16511.1]; exact data_16_16511.2.2
  · rw [data_16_16511.2.1]; decide

end Collatz.Research.FirstDescent.Batch054
