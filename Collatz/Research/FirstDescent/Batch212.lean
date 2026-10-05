import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 212. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch212
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 245231). -/
theorem data_18_245231 : oddCount 245231 18 = 11 ∧
    acceleratedOrbit 18 245231 = 165719 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_245231 : ∀ j : Fin 18,
    245231 ≤ acceleratedOrbit j.val 245231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_245231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 245231) = 177147 * m + 165719 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 245231
  rw [data_18_245231.1, data_18_245231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_245231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 245231) < 262144 * m + 245231 := by
  apply descent_of_endpoint
  · rw [data_18_245231.1]; exact data_18_245231.2.2
  · rw [data_18_245231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 245851). -/
theorem data_18_245851 : oddCount 245851 18 = 11 ∧
    acceleratedOrbit 18 245851 = 166138 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_245851 : ∀ j : Fin 18,
    245851 ≤ acceleratedOrbit j.val 245851 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_245851 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 245851) = 177147 * m + 166138 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 245851
  rw [data_18_245851.1, data_18_245851.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_245851 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 245851) < 262144 * m + 245851 := by
  apply descent_of_endpoint
  · rw [data_18_245851.1]; exact data_18_245851.2.2
  · rw [data_18_245851.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 246655). -/
theorem data_18_246655 : oddCount 246655 18 = 11 ∧
    acceleratedOrbit 18 246655 = 166681 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_246655 : ∀ j : Fin 18,
    246655 ≤ acceleratedOrbit j.val 246655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_246655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246655) = 177147 * m + 166681 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 246655
  rw [data_18_246655.1, data_18_246655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_246655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246655) < 262144 * m + 246655 := by
  apply descent_of_endpoint
  · rw [data_18_246655.1]; exact data_18_246655.2.2
  · rw [data_18_246655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 246687). -/
theorem data_18_246687 : oddCount 246687 18 = 11 ∧
    acceleratedOrbit 18 246687 = 166703 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_246687 : ∀ j : Fin 18,
    246687 ≤ acceleratedOrbit j.val 246687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_246687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246687) = 177147 * m + 166703 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 246687
  rw [data_18_246687.1, data_18_246687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_246687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246687) < 262144 * m + 246687 := by
  apply descent_of_endpoint
  · rw [data_18_246687.1]; exact data_18_246687.2.2
  · rw [data_18_246687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 246767). -/
theorem data_18_246767 : oddCount 246767 18 = 11 ∧
    acceleratedOrbit 18 246767 = 166757 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_246767 : ∀ j : Fin 18,
    246767 ≤ acceleratedOrbit j.val 246767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_246767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246767) = 177147 * m + 166757 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 246767
  rw [data_18_246767.1, data_18_246767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_246767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246767) < 262144 * m + 246767 := by
  apply descent_of_endpoint
  · rw [data_18_246767.1]; exact data_18_246767.2.2
  · rw [data_18_246767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 246855). -/
theorem data_18_246855 : oddCount 246855 18 = 11 ∧
    acceleratedOrbit 18 246855 = 166817 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_246855 : ∀ j : Fin 18,
    246855 ≤ acceleratedOrbit j.val 246855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_246855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246855) = 177147 * m + 166817 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 246855
  rw [data_18_246855.1, data_18_246855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_246855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246855) < 262144 * m + 246855 := by
  apply descent_of_endpoint
  · rw [data_18_246855.1]; exact data_18_246855.2.2
  · rw [data_18_246855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 246887). -/
theorem data_18_246887 : oddCount 246887 18 = 11 ∧
    acceleratedOrbit 18 246887 = 166838 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_246887 : ∀ j : Fin 18,
    246887 ≤ acceleratedOrbit j.val 246887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_246887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246887) = 177147 * m + 166838 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 246887
  rw [data_18_246887.1, data_18_246887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_246887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 246887) < 262144 * m + 246887 := by
  apply descent_of_endpoint
  · rw [data_18_246887.1]; exact data_18_246887.2.2
  · rw [data_18_246887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 247167). -/
theorem data_18_247167 : oddCount 247167 18 = 11 ∧
    acceleratedOrbit 18 247167 = 167027 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_247167 : ∀ j : Fin 18,
    247167 ≤ acceleratedOrbit j.val 247167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_247167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247167) = 177147 * m + 167027 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 247167
  rw [data_18_247167.1, data_18_247167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_247167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247167) < 262144 * m + 247167 := by
  apply descent_of_endpoint
  · rw [data_18_247167.1]; exact data_18_247167.2.2
  · rw [data_18_247167.2.1]; decide

end Collatz.Research.FirstDescent.Batch212
