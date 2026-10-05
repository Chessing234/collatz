import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 102. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch102
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 5167). -/
theorem data_18_5167 : oddCount 5167 18 = 11 ∧
    acceleratedOrbit 18 5167 = 3493 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_5167 : ∀ j : Fin 18,
    5167 ≤ acceleratedOrbit j.val 5167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_5167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5167) = 177147 * m + 3493 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 5167
  rw [data_18_5167.1, data_18_5167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_5167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5167) < 262144 * m + 5167 := by
  apply descent_of_endpoint
  · rw [data_18_5167.1]; exact data_18_5167.2.2
  · rw [data_18_5167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 5287). -/
theorem data_18_5287 : oddCount 5287 18 = 11 ∧
    acceleratedOrbit 18 5287 = 3574 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_5287 : ∀ j : Fin 18,
    5287 ≤ acceleratedOrbit j.val 5287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_5287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5287) = 177147 * m + 3574 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 5287
  rw [data_18_5287.1, data_18_5287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_5287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5287) < 262144 * m + 5287 := by
  apply descent_of_endpoint
  · rw [data_18_5287.1]; exact data_18_5287.2.2
  · rw [data_18_5287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 5839). -/
theorem data_18_5839 : oddCount 5839 18 = 11 ∧
    acceleratedOrbit 18 5839 = 3947 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_5839 : ∀ j : Fin 18,
    5839 ≤ acceleratedOrbit j.val 5839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_5839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5839) = 177147 * m + 3947 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 5839
  rw [data_18_5839.1, data_18_5839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_5839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5839) < 262144 * m + 5839 := by
  apply descent_of_endpoint
  · rw [data_18_5839.1]; exact data_18_5839.2.2
  · rw [data_18_5839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 5999). -/
theorem data_18_5999 : oddCount 5999 18 = 11 ∧
    acceleratedOrbit 18 5999 = 4055 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_5999 : ∀ j : Fin 18,
    5999 ≤ acceleratedOrbit j.val 5999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_5999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5999) = 177147 * m + 4055 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 5999
  rw [data_18_5999.1, data_18_5999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_5999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 5999) < 262144 * m + 5999 := by
  apply descent_of_endpoint
  · rw [data_18_5999.1]; exact data_18_5999.2.2
  · rw [data_18_5999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6055). -/
theorem data_18_6055 : oddCount 6055 18 = 11 ∧
    acceleratedOrbit 18 6055 = 4093 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6055 : ∀ j : Fin 18,
    6055 ≤ acceleratedOrbit j.val 6055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6055) = 177147 * m + 4093 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6055
  rw [data_18_6055.1, data_18_6055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6055) < 262144 * m + 6055 := by
  apply descent_of_endpoint
  · rw [data_18_6055.1]; exact data_18_6055.2.2
  · rw [data_18_6055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6079). -/
theorem data_18_6079 : oddCount 6079 18 = 11 ∧
    acceleratedOrbit 18 6079 = 4109 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6079 : ∀ j : Fin 18,
    6079 ≤ acceleratedOrbit j.val 6079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6079) = 177147 * m + 4109 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6079
  rw [data_18_6079.1, data_18_6079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6079) < 262144 * m + 6079 := by
  apply descent_of_endpoint
  · rw [data_18_6079.1]; exact data_18_6079.2.2
  · rw [data_18_6079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6139). -/
theorem data_18_6139 : oddCount 6139 18 = 11 ∧
    acceleratedOrbit 18 6139 = 4150 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6139 : ∀ j : Fin 18,
    6139 ≤ acceleratedOrbit j.val 6139 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6139 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6139) = 177147 * m + 4150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6139
  rw [data_18_6139.1, data_18_6139.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6139 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6139) < 262144 * m + 6139 := by
  apply descent_of_endpoint
  · rw [data_18_6139.1]; exact data_18_6139.2.2
  · rw [data_18_6139.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6367). -/
theorem data_18_6367 : oddCount 6367 18 = 11 ∧
    acceleratedOrbit 18 6367 = 4304 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6367 : ∀ j : Fin 18,
    6367 ≤ acceleratedOrbit j.val 6367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6367) = 177147 * m + 4304 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6367
  rw [data_18_6367.1, data_18_6367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6367) < 262144 * m + 6367 := by
  apply descent_of_endpoint
  · rw [data_18_6367.1]; exact data_18_6367.2.2
  · rw [data_18_6367.2.1]; decide

end Collatz.Research.FirstDescent.Batch102
