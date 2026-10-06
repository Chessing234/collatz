import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 71. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch071
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34271). -/
theorem data_16_34271 : oddCount 34271 16 = 10 ∧
    acceleratedOrbit 16 34271 = 30880 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34271 : ∀ j : Fin 16,
    34271 ≤ acceleratedOrbit j.val 34271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34271) = 59049 * m + 30880 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34271
  rw [data_16_34271.1, data_16_34271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34271) < 65536 * m + 34271 := by
  apply descent_of_endpoint
  · rw [data_16_34271.1]; exact data_16_34271.2.2
  · rw [data_16_34271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34535). -/
theorem data_16_34535 : oddCount 34535 16 = 10 ∧
    acceleratedOrbit 16 34535 = 31118 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34535 : ∀ j : Fin 16,
    34535 ≤ acceleratedOrbit j.val 34535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34535) = 59049 * m + 31118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34535
  rw [data_16_34535.1, data_16_34535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34535) < 65536 * m + 34535 := by
  apply descent_of_endpoint
  · rw [data_16_34535.1]; exact data_16_34535.2.2
  · rw [data_16_34535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34631). -/
theorem data_16_34631 : oddCount 34631 16 = 10 ∧
    acceleratedOrbit 16 34631 = 31205 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34631 : ∀ j : Fin 16,
    34631 ≤ acceleratedOrbit j.val 34631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34631 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34631) = 59049 * m + 31205 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34631
  rw [data_16_34631.1, data_16_34631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34631 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34631) < 65536 * m + 34631 := by
  apply descent_of_endpoint
  · rw [data_16_34631.1]; exact data_16_34631.2.2
  · rw [data_16_34631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34651). -/
theorem data_16_34651 : oddCount 34651 16 = 10 ∧
    acceleratedOrbit 16 34651 = 31223 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34651 : ∀ j : Fin 16,
    34651 ≤ acceleratedOrbit j.val 34651 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34651 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34651) = 59049 * m + 31223 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34651
  rw [data_16_34651.1, data_16_34651.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34651 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34651) < 65536 * m + 34651 := by
  apply descent_of_endpoint
  · rw [data_16_34651.1]; exact data_16_34651.2.2
  · rw [data_16_34651.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 34927). -/
theorem data_16_34927 : oddCount 34927 16 = 10 ∧
    acceleratedOrbit 16 34927 = 31471 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_34927 : ∀ j : Fin 16,
    34927 ≤ acceleratedOrbit j.val 34927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_34927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34927) = 59049 * m + 31471 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 34927
  rw [data_16_34927.1, data_16_34927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_34927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 34927) < 65536 * m + 34927 := by
  apply descent_of_endpoint
  · rw [data_16_34927.1]; exact data_16_34927.2.2
  · rw [data_16_34927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 35023). -/
theorem data_16_35023 : oddCount 35023 16 = 10 ∧
    acceleratedOrbit 16 35023 = 31558 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_35023 : ∀ j : Fin 16,
    35023 ≤ acceleratedOrbit j.val 35023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_35023 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35023) = 59049 * m + 31558 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 35023
  rw [data_16_35023.1, data_16_35023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_35023 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35023) < 65536 * m + 35023 := by
  apply descent_of_endpoint
  · rw [data_16_35023.1]; exact data_16_35023.2.2
  · rw [data_16_35023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 35231). -/
theorem data_16_35231 : oddCount 35231 16 = 10 ∧
    acceleratedOrbit 16 35231 = 31745 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_35231 : ∀ j : Fin 16,
    35231 ≤ acceleratedOrbit j.val 35231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_35231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35231) = 59049 * m + 31745 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 35231
  rw [data_16_35231.1, data_16_35231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_35231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35231) < 65536 * m + 35231 := by
  apply descent_of_endpoint
  · rw [data_16_35231.1]; exact data_16_35231.2.2
  · rw [data_16_35231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 35279). -/
theorem data_16_35279 : oddCount 35279 16 = 10 ∧
    acceleratedOrbit 16 35279 = 31789 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_35279 : ∀ j : Fin 16,
    35279 ≤ acceleratedOrbit j.val 35279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_35279 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35279) = 59049 * m + 31789 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 35279
  rw [data_16_35279.1, data_16_35279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_35279 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35279) < 65536 * m + 35279 := by
  apply descent_of_endpoint
  · rw [data_16_35279.1]; exact data_16_35279.2.2
  · rw [data_16_35279.2.1]; decide

end Collatz.Research.FirstDescent.Batch071
