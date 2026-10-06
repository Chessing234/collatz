import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 77. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch077
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 40687). -/
theorem data_16_40687 : oddCount 40687 16 = 10 ∧
    acceleratedOrbit 16 40687 = 36661 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_40687 : ∀ j : Fin 16,
    40687 ≤ acceleratedOrbit j.val 40687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_40687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40687) = 59049 * m + 36661 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 40687
  rw [data_16_40687.1, data_16_40687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_40687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40687) < 65536 * m + 40687 := by
  apply descent_of_endpoint
  · rw [data_16_40687.1]; exact data_16_40687.2.2
  · rw [data_16_40687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 40943). -/
theorem data_16_40943 : oddCount 40943 16 = 10 ∧
    acceleratedOrbit 16 40943 = 36892 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_40943 : ∀ j : Fin 16,
    40943 ≤ acceleratedOrbit j.val 40943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_40943 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40943) = 59049 * m + 36892 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 40943
  rw [data_16_40943.1, data_16_40943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_40943 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40943) < 65536 * m + 40943 := by
  apply descent_of_endpoint
  · rw [data_16_40943.1]; exact data_16_40943.2.2
  · rw [data_16_40943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 41023). -/
theorem data_16_41023 : oddCount 41023 16 = 10 ∧
    acceleratedOrbit 16 41023 = 36964 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_41023 : ∀ j : Fin 16,
    41023 ≤ acceleratedOrbit j.val 41023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_41023 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41023) = 59049 * m + 36964 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 41023
  rw [data_16_41023.1, data_16_41023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_41023 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41023) < 65536 * m + 41023 := by
  apply descent_of_endpoint
  · rw [data_16_41023.1]; exact data_16_41023.2.2
  · rw [data_16_41023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 41063). -/
theorem data_16_41063 : oddCount 41063 16 = 10 ∧
    acceleratedOrbit 16 41063 = 37000 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_41063 : ∀ j : Fin 16,
    41063 ≤ acceleratedOrbit j.val 41063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_41063 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41063) = 59049 * m + 37000 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 41063
  rw [data_16_41063.1, data_16_41063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_41063 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41063) < 65536 * m + 41063 := by
  apply descent_of_endpoint
  · rw [data_16_41063.1]; exact data_16_41063.2.2
  · rw [data_16_41063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 41183). -/
theorem data_16_41183 : oddCount 41183 16 = 10 ∧
    acceleratedOrbit 16 41183 = 37108 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_41183 : ∀ j : Fin 16,
    41183 ≤ acceleratedOrbit j.val 41183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_41183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41183) = 59049 * m + 37108 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 41183
  rw [data_16_41183.1, data_16_41183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_41183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41183) < 65536 * m + 41183 := by
  apply descent_of_endpoint
  · rw [data_16_41183.1]; exact data_16_41183.2.2
  · rw [data_16_41183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 41243). -/
theorem data_16_41243 : oddCount 41243 16 = 10 ∧
    acceleratedOrbit 16 41243 = 37162 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_41243 : ∀ j : Fin 16,
    41243 ≤ acceleratedOrbit j.val 41243 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_41243 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41243) = 59049 * m + 37162 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 41243
  rw [data_16_41243.1, data_16_41243.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_41243 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41243) < 65536 * m + 41243 := by
  apply descent_of_endpoint
  · rw [data_16_41243.1]; exact data_16_41243.2.2
  · rw [data_16_41243.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 41447). -/
theorem data_16_41447 : oddCount 41447 16 = 10 ∧
    acceleratedOrbit 16 41447 = 37346 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_41447 : ∀ j : Fin 16,
    41447 ≤ acceleratedOrbit j.val 41447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_41447 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41447) = 59049 * m + 37346 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 41447
  rw [data_16_41447.1, data_16_41447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_41447 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41447) < 65536 * m + 41447 := by
  apply descent_of_endpoint
  · rw [data_16_41447.1]; exact data_16_41447.2.2
  · rw [data_16_41447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 41627). -/
theorem data_16_41627 : oddCount 41627 16 = 10 ∧
    acceleratedOrbit 16 41627 = 37508 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_41627 : ∀ j : Fin 16,
    41627 ≤ acceleratedOrbit j.val 41627 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_41627 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41627) = 59049 * m + 37508 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 41627
  rw [data_16_41627.1, data_16_41627.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_41627 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 41627) < 65536 * m + 41627 := by
  apply descent_of_endpoint
  · rw [data_16_41627.1]; exact data_16_41627.2.2
  · rw [data_16_41627.2.1]; decide

end Collatz.Research.FirstDescent.Batch077
