import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 51. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch051
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13279). -/
theorem data_16_13279 : oddCount 13279 16 = 10 ∧
    acceleratedOrbit 16 13279 = 11966 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13279 : ∀ j : Fin 16,
    13279 ≤ acceleratedOrbit j.val 13279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13279 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13279) = 59049 * m + 11966 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13279
  rw [data_16_13279.1, data_16_13279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13279 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13279) < 65536 * m + 13279 := by
  apply descent_of_endpoint
  · rw [data_16_13279.1]; exact data_16_13279.2.2
  · rw [data_16_13279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13339). -/
theorem data_16_13339 : oddCount 13339 16 = 10 ∧
    acceleratedOrbit 16 13339 = 12020 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13339 : ∀ j : Fin 16,
    13339 ≤ acceleratedOrbit j.val 13339 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13339 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13339) = 59049 * m + 12020 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13339
  rw [data_16_13339.1, data_16_13339.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13339 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13339) < 65536 * m + 13339 := by
  apply descent_of_endpoint
  · rw [data_16_13339.1]; exact data_16_13339.2.2
  · rw [data_16_13339.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13535). -/
theorem data_16_13535 : oddCount 13535 16 = 10 ∧
    acceleratedOrbit 16 13535 = 12197 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13535 : ∀ j : Fin 16,
    13535 ≤ acceleratedOrbit j.val 13535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13535) = 59049 * m + 12197 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13535
  rw [data_16_13535.1, data_16_13535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13535) < 65536 * m + 13535 := by
  apply descent_of_endpoint
  · rw [data_16_13535.1]; exact data_16_13535.2.2
  · rw [data_16_13535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13615). -/
theorem data_16_13615 : oddCount 13615 16 = 10 ∧
    acceleratedOrbit 16 13615 = 12269 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13615 : ∀ j : Fin 16,
    13615 ≤ acceleratedOrbit j.val 13615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13615) = 59049 * m + 12269 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13615
  rw [data_16_13615.1, data_16_13615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13615) < 65536 * m + 13615 := by
  apply descent_of_endpoint
  · rw [data_16_13615.1]; exact data_16_13615.2.2
  · rw [data_16_13615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13671). -/
theorem data_16_13671 : oddCount 13671 16 = 10 ∧
    acceleratedOrbit 16 13671 = 12319 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13671 : ∀ j : Fin 16,
    13671 ≤ acceleratedOrbit j.val 13671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13671) = 59049 * m + 12319 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13671
  rw [data_16_13671.1, data_16_13671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13671) < 65536 * m + 13671 := by
  apply descent_of_endpoint
  · rw [data_16_13671.1]; exact data_16_13671.2.2
  · rw [data_16_13671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13855). -/
theorem data_16_13855 : oddCount 13855 16 = 10 ∧
    acceleratedOrbit 16 13855 = 12485 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13855 : ∀ j : Fin 16,
    13855 ≤ acceleratedOrbit j.val 13855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13855 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13855) = 59049 * m + 12485 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13855
  rw [data_16_13855.1, data_16_13855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13855 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13855) < 65536 * m + 13855 := by
  apply descent_of_endpoint
  · rw [data_16_13855.1]; exact data_16_13855.2.2
  · rw [data_16_13855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13927). -/
theorem data_16_13927 : oddCount 13927 16 = 10 ∧
    acceleratedOrbit 16 13927 = 12550 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13927 : ∀ j : Fin 16,
    13927 ≤ acceleratedOrbit j.val 13927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13927) = 59049 * m + 12550 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13927
  rw [data_16_13927.1, data_16_13927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13927) < 65536 * m + 13927 := by
  apply descent_of_endpoint
  · rw [data_16_13927.1]; exact data_16_13927.2.2
  · rw [data_16_13927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 13951). -/
theorem data_16_13951 : oddCount 13951 16 = 10 ∧
    acceleratedOrbit 16 13951 = 12571 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_13951 : ∀ j : Fin 16,
    13951 ≤ acceleratedOrbit j.val 13951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_13951 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13951) = 59049 * m + 12571 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 13951
  rw [data_16_13951.1, data_16_13951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_13951 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 13951) < 65536 * m + 13951 := by
  apply descent_of_endpoint
  · rw [data_16_13951.1]; exact data_16_13951.2.2
  · rw [data_16_13951.2.1]; decide

end Collatz.Research.FirstDescent.Batch051
