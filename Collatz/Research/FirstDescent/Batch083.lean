import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 83. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch083
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 47423). -/
theorem data_16_47423 : oddCount 47423 16 = 10 ∧
    acceleratedOrbit 16 47423 = 42730 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_47423 : ∀ j : Fin 16,
    47423 ≤ acceleratedOrbit j.val 47423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_47423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47423) = 59049 * m + 42730 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 47423
  rw [data_16_47423.1, data_16_47423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_47423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47423) < 65536 * m + 47423 := by
  apply descent_of_endpoint
  · rw [data_16_47423.1]; exact data_16_47423.2.2
  · rw [data_16_47423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 47487). -/
theorem data_16_47487 : oddCount 47487 16 = 10 ∧
    acceleratedOrbit 16 47487 = 42788 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_47487 : ∀ j : Fin 16,
    47487 ≤ acceleratedOrbit j.val 47487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_47487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47487) = 59049 * m + 42788 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 47487
  rw [data_16_47487.1, data_16_47487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_47487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47487) < 65536 * m + 47487 := by
  apply descent_of_endpoint
  · rw [data_16_47487.1]; exact data_16_47487.2.2
  · rw [data_16_47487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 47807). -/
theorem data_16_47807 : oddCount 47807 16 = 10 ∧
    acceleratedOrbit 16 47807 = 43076 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_47807 : ∀ j : Fin 16,
    47807 ≤ acceleratedOrbit j.val 47807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_47807 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47807) = 59049 * m + 43076 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 47807
  rw [data_16_47807.1, data_16_47807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_47807 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47807) < 65536 * m + 47807 := by
  apply descent_of_endpoint
  · rw [data_16_47807.1]; exact data_16_47807.2.2
  · rw [data_16_47807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 48095). -/
theorem data_16_48095 : oddCount 48095 16 = 10 ∧
    acceleratedOrbit 16 48095 = 43336 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_48095 : ∀ j : Fin 16,
    48095 ≤ acceleratedOrbit j.val 48095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_48095 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48095) = 59049 * m + 43336 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 48095
  rw [data_16_48095.1, data_16_48095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_48095 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48095) < 65536 * m + 48095 := by
  apply descent_of_endpoint
  · rw [data_16_48095.1]; exact data_16_48095.2.2
  · rw [data_16_48095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 48155). -/
theorem data_16_48155 : oddCount 48155 16 = 10 ∧
    acceleratedOrbit 16 48155 = 43390 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_48155 : ∀ j : Fin 16,
    48155 ≤ acceleratedOrbit j.val 48155 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_48155 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48155) = 59049 * m + 43390 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 48155
  rw [data_16_48155.1, data_16_48155.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_48155 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48155) < 65536 * m + 48155 := by
  apply descent_of_endpoint
  · rw [data_16_48155.1]; exact data_16_48155.2.2
  · rw [data_16_48155.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 48295). -/
theorem data_16_48295 : oddCount 48295 16 = 10 ∧
    acceleratedOrbit 16 48295 = 43516 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_48295 : ∀ j : Fin 16,
    48295 ≤ acceleratedOrbit j.val 48295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_48295 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48295) = 59049 * m + 43516 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 48295
  rw [data_16_48295.1, data_16_48295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_48295 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48295) < 65536 * m + 48295 := by
  apply descent_of_endpoint
  · rw [data_16_48295.1]; exact data_16_48295.2.2
  · rw [data_16_48295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 48379). -/
theorem data_16_48379 : oddCount 48379 16 = 10 ∧
    acceleratedOrbit 16 48379 = 43592 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_48379 : ∀ j : Fin 16,
    48379 ≤ acceleratedOrbit j.val 48379 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_48379 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48379) = 59049 * m + 43592 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 48379
  rw [data_16_48379.1, data_16_48379.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_48379 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48379) < 65536 * m + 48379 := by
  apply descent_of_endpoint
  · rw [data_16_48379.1]; exact data_16_48379.2.2
  · rw [data_16_48379.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 48879). -/
theorem data_16_48879 : oddCount 48879 16 = 10 ∧
    acceleratedOrbit 16 48879 = 44042 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_48879 : ∀ j : Fin 16,
    48879 ≤ acceleratedOrbit j.val 48879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_48879 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48879) = 59049 * m + 44042 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 48879
  rw [data_16_48879.1, data_16_48879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_48879 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48879) < 65536 * m + 48879 := by
  apply descent_of_endpoint
  · rw [data_16_48879.1]; exact data_16_48879.2.2
  · rw [data_16_48879.2.1]; decide

end Collatz.Research.FirstDescent.Batch083
