import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 75. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch075
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 38271). -/
theorem data_16_38271 : oddCount 38271 16 = 10 ∧
    acceleratedOrbit 16 38271 = 34484 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_38271 : ∀ j : Fin 16,
    38271 ≤ acceleratedOrbit j.val 38271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_38271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38271) = 59049 * m + 34484 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 38271
  rw [data_16_38271.1, data_16_38271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_38271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38271) < 65536 * m + 38271 := by
  apply descent_of_endpoint
  · rw [data_16_38271.1]; exact data_16_38271.2.2
  · rw [data_16_38271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 38427). -/
theorem data_16_38427 : oddCount 38427 16 = 10 ∧
    acceleratedOrbit 16 38427 = 34625 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_38427 : ∀ j : Fin 16,
    38427 ≤ acceleratedOrbit j.val 38427 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_38427 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38427) = 59049 * m + 34625 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 38427
  rw [data_16_38427.1, data_16_38427.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_38427 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38427) < 65536 * m + 38427 := by
  apply descent_of_endpoint
  · rw [data_16_38427.1]; exact data_16_38427.2.2
  · rw [data_16_38427.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 38607). -/
theorem data_16_38607 : oddCount 38607 16 = 10 ∧
    acceleratedOrbit 16 38607 = 34787 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_38607 : ∀ j : Fin 16,
    38607 ≤ acceleratedOrbit j.val 38607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_38607 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38607) = 59049 * m + 34787 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 38607
  rw [data_16_38607.1, data_16_38607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_38607 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38607) < 65536 * m + 38607 := by
  apply descent_of_endpoint
  · rw [data_16_38607.1]; exact data_16_38607.2.2
  · rw [data_16_38607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 38847). -/
theorem data_16_38847 : oddCount 38847 16 = 10 ∧
    acceleratedOrbit 16 38847 = 35003 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_38847 : ∀ j : Fin 16,
    38847 ≤ acceleratedOrbit j.val 38847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_38847 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38847) = 59049 * m + 35003 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 38847
  rw [data_16_38847.1, data_16_38847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_38847 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38847) < 65536 * m + 38847 := by
  apply descent_of_endpoint
  · rw [data_16_38847.1]; exact data_16_38847.2.2
  · rw [data_16_38847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 39039). -/
theorem data_16_39039 : oddCount 39039 16 = 10 ∧
    acceleratedOrbit 16 39039 = 35176 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_39039 : ∀ j : Fin 16,
    39039 ≤ acceleratedOrbit j.val 39039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_39039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39039) = 59049 * m + 35176 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 39039
  rw [data_16_39039.1, data_16_39039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_39039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39039) < 65536 * m + 39039 := by
  apply descent_of_endpoint
  · rw [data_16_39039.1]; exact data_16_39039.2.2
  · rw [data_16_39039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 39135). -/
theorem data_16_39135 : oddCount 39135 16 = 10 ∧
    acceleratedOrbit 16 39135 = 35263 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_39135 : ∀ j : Fin 16,
    39135 ≤ acceleratedOrbit j.val 39135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_39135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39135) = 59049 * m + 35263 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 39135
  rw [data_16_39135.1, data_16_39135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_39135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39135) < 65536 * m + 39135 := by
  apply descent_of_endpoint
  · rw [data_16_39135.1]; exact data_16_39135.2.2
  · rw [data_16_39135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 39195). -/
theorem data_16_39195 : oddCount 39195 16 = 10 ∧
    acceleratedOrbit 16 39195 = 35317 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_39195 : ∀ j : Fin 16,
    39195 ≤ acceleratedOrbit j.val 39195 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_39195 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39195) = 59049 * m + 35317 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 39195
  rw [data_16_39195.1, data_16_39195.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_39195 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39195) < 65536 * m + 39195 := by
  apply descent_of_endpoint
  · rw [data_16_39195.1]; exact data_16_39195.2.2
  · rw [data_16_39195.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 39295). -/
theorem data_16_39295 : oddCount 39295 16 = 10 ∧
    acceleratedOrbit 16 39295 = 35407 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_39295 : ∀ j : Fin 16,
    39295 ≤ acceleratedOrbit j.val 39295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_39295 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39295) = 59049 * m + 35407 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 39295
  rw [data_16_39295.1, data_16_39295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_39295 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39295) < 65536 * m + 39295 := by
  apply descent_of_endpoint
  · rw [data_16_39295.1]; exact data_16_39295.2.2
  · rw [data_16_39295.2.1]; decide

end Collatz.Research.FirstDescent.Batch075
