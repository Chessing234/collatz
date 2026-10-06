import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 66. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch066
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28447). -/
theorem data_16_28447 : oddCount 28447 16 = 10 ∧
    acceleratedOrbit 16 28447 = 25633 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28447 : ∀ j : Fin 16,
    28447 ≤ acceleratedOrbit j.val 28447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28447 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28447) = 59049 * m + 25633 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28447
  rw [data_16_28447.1, data_16_28447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28447 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28447) < 65536 * m + 28447 := by
  apply descent_of_endpoint
  · rw [data_16_28447.1]; exact data_16_28447.2.2
  · rw [data_16_28447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28507). -/
theorem data_16_28507 : oddCount 28507 16 = 10 ∧
    acceleratedOrbit 16 28507 = 25687 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28507 : ∀ j : Fin 16,
    28507 ≤ acceleratedOrbit j.val 28507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28507 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28507) = 59049 * m + 25687 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28507
  rw [data_16_28507.1, data_16_28507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28507 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28507) < 65536 * m + 28507 := by
  apply descent_of_endpoint
  · rw [data_16_28507.1]; exact data_16_28507.2.2
  · rw [data_16_28507.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28527). -/
theorem data_16_28527 : oddCount 28527 16 = 10 ∧
    acceleratedOrbit 16 28527 = 25705 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28527 : ∀ j : Fin 16,
    28527 ≤ acceleratedOrbit j.val 28527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28527 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28527) = 59049 * m + 25705 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28527
  rw [data_16_28527.1, data_16_28527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28527 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28527) < 65536 * m + 28527 := by
  apply descent_of_endpoint
  · rw [data_16_28527.1]; exact data_16_28527.2.2
  · rw [data_16_28527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28927). -/
theorem data_16_28927 : oddCount 28927 16 = 10 ∧
    acceleratedOrbit 16 28927 = 26065 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28927 : ∀ j : Fin 16,
    28927 ≤ acceleratedOrbit j.val 28927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28927) = 59049 * m + 26065 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28927
  rw [data_16_28927.1, data_16_28927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28927) < 65536 * m + 28927 := by
  apply descent_of_endpoint
  · rw [data_16_28927.1]; exact data_16_28927.2.2
  · rw [data_16_28927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 29087). -/
theorem data_16_29087 : oddCount 29087 16 = 10 ∧
    acceleratedOrbit 16 29087 = 26209 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_29087 : ∀ j : Fin 16,
    29087 ≤ acceleratedOrbit j.val 29087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_29087 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29087) = 59049 * m + 26209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 29087
  rw [data_16_29087.1, data_16_29087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_29087 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29087) < 65536 * m + 29087 := by
  apply descent_of_endpoint
  · rw [data_16_29087.1]; exact data_16_29087.2.2
  · rw [data_16_29087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 29231). -/
theorem data_16_29231 : oddCount 29231 16 = 10 ∧
    acceleratedOrbit 16 29231 = 26339 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_29231 : ∀ j : Fin 16,
    29231 ≤ acceleratedOrbit j.val 29231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_29231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29231) = 59049 * m + 26339 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 29231
  rw [data_16_29231.1, data_16_29231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_29231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29231) < 65536 * m + 29231 := by
  apply descent_of_endpoint
  · rw [data_16_29231.1]; exact data_16_29231.2.2
  · rw [data_16_29231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 29631). -/
theorem data_16_29631 : oddCount 29631 16 = 10 ∧
    acceleratedOrbit 16 29631 = 26699 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_29631 : ∀ j : Fin 16,
    29631 ≤ acceleratedOrbit j.val 29631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_29631 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29631) = 59049 * m + 26699 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 29631
  rw [data_16_29631.1, data_16_29631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_29631 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29631) < 65536 * m + 29631 := by
  apply descent_of_endpoint
  · rw [data_16_29631.1]; exact data_16_29631.2.2
  · rw [data_16_29631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 29807). -/
theorem data_16_29807 : oddCount 29807 16 = 10 ∧
    acceleratedOrbit 16 29807 = 26858 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_29807 : ∀ j : Fin 16,
    29807 ≤ acceleratedOrbit j.val 29807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_29807 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29807) = 59049 * m + 26858 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 29807
  rw [data_16_29807.1, data_16_29807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_29807 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 29807) < 65536 * m + 29807 := by
  apply descent_of_endpoint
  · rw [data_16_29807.1]; exact data_16_29807.2.2
  · rw [data_16_29807.2.1]; decide

end Collatz.Research.FirstDescent.Batch066
