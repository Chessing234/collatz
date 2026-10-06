import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 172. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch172
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 155291). -/
theorem data_18_155291 : oddCount 155291 18 = 11 ∧
    acceleratedOrbit 18 155291 = 104941 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_155291 : ∀ j : Fin 18,
    155291 ≤ acceleratedOrbit j.val 155291 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_155291 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155291) = 177147 * m + 104941 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 155291
  rw [data_18_155291.1, data_18_155291.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_155291 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155291) < 262144 * m + 155291 := by
  apply descent_of_endpoint
  · rw [data_18_155291.1]; exact data_18_155291.2.2
  · rw [data_18_155291.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 155327). -/
theorem data_18_155327 : oddCount 155327 18 = 11 ∧
    acceleratedOrbit 18 155327 = 104965 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_155327 : ∀ j : Fin 18,
    155327 ≤ acceleratedOrbit j.val 155327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_155327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155327) = 177147 * m + 104965 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 155327
  rw [data_18_155327.1, data_18_155327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_155327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155327) < 262144 * m + 155327 := by
  apply descent_of_endpoint
  · rw [data_18_155327.1]; exact data_18_155327.2.2
  · rw [data_18_155327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 155483). -/
theorem data_18_155483 : oddCount 155483 18 = 11 ∧
    acceleratedOrbit 18 155483 = 105071 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_155483 : ∀ j : Fin 18,
    155483 ≤ acceleratedOrbit j.val 155483 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_155483 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155483) = 177147 * m + 105071 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 155483
  rw [data_18_155483.1, data_18_155483.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_155483 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155483) < 262144 * m + 155483 := by
  apply descent_of_endpoint
  · rw [data_18_155483.1]; exact data_18_155483.2.2
  · rw [data_18_155483.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 155519). -/
theorem data_18_155519 : oddCount 155519 18 = 11 ∧
    acceleratedOrbit 18 155519 = 105095 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_155519 : ∀ j : Fin 18,
    155519 ≤ acceleratedOrbit j.val 155519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_155519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155519) = 177147 * m + 105095 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 155519
  rw [data_18_155519.1, data_18_155519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_155519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155519) < 262144 * m + 155519 := by
  apply descent_of_endpoint
  · rw [data_18_155519.1]; exact data_18_155519.2.2
  · rw [data_18_155519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 155679). -/
theorem data_18_155679 : oddCount 155679 18 = 11 ∧
    acceleratedOrbit 18 155679 = 105203 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_155679 : ∀ j : Fin 18,
    155679 ≤ acceleratedOrbit j.val 155679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_155679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155679) = 177147 * m + 105203 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 155679
  rw [data_18_155679.1, data_18_155679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_155679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155679) < 262144 * m + 155679 := by
  apply descent_of_endpoint
  · rw [data_18_155679.1]; exact data_18_155679.2.2
  · rw [data_18_155679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 156251). -/
theorem data_18_156251 : oddCount 156251 18 = 11 ∧
    acceleratedOrbit 18 156251 = 105590 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_156251 : ∀ j : Fin 18,
    156251 ≤ acceleratedOrbit j.val 156251 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_156251 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 156251) = 177147 * m + 105590 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 156251
  rw [data_18_156251.1, data_18_156251.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_156251 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 156251) < 262144 * m + 156251 := by
  apply descent_of_endpoint
  · rw [data_18_156251.1]; exact data_18_156251.2.2
  · rw [data_18_156251.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 157275). -/
theorem data_18_157275 : oddCount 157275 18 = 11 ∧
    acceleratedOrbit 18 157275 = 106282 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_157275 : ∀ j : Fin 18,
    157275 ≤ acceleratedOrbit j.val 157275 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_157275 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157275) = 177147 * m + 106282 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 157275
  rw [data_18_157275.1, data_18_157275.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_157275 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157275) < 262144 * m + 157275 := by
  apply descent_of_endpoint
  · rw [data_18_157275.1]; exact data_18_157275.2.2
  · rw [data_18_157275.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 157391). -/
theorem data_18_157391 : oddCount 157391 18 = 11 ∧
    acceleratedOrbit 18 157391 = 106360 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_157391 : ∀ j : Fin 18,
    157391 ≤ acceleratedOrbit j.val 157391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_157391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157391) = 177147 * m + 106360 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 157391
  rw [data_18_157391.1, data_18_157391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_157391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 157391) < 262144 * m + 157391 := by
  apply descent_of_endpoint
  · rw [data_18_157391.1]; exact data_18_157391.2.2
  · rw [data_18_157391.2.1]; decide

end Collatz.Research.FirstDescent.Batch172
