import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 101. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch101
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 3263). -/
theorem data_18_3263 : oddCount 3263 18 = 11 ∧
    acceleratedOrbit 18 3263 = 2206 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_3263 : ∀ j : Fin 18,
    3263 ≤ acceleratedOrbit j.val 3263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_3263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3263) = 177147 * m + 2206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 3263
  rw [data_18_3263.1, data_18_3263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_3263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3263) < 262144 * m + 3263 := by
  apply descent_of_endpoint
  · rw [data_18_3263.1]; exact data_18_3263.2.2
  · rw [data_18_3263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 3327). -/
theorem data_18_3327 : oddCount 3327 18 = 11 ∧
    acceleratedOrbit 18 3327 = 2249 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_3327 : ∀ j : Fin 18,
    3327 ≤ acceleratedOrbit j.val 3327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_3327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3327) = 177147 * m + 2249 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 3327
  rw [data_18_3327.1, data_18_3327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_3327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3327) < 262144 * m + 3327 := by
  apply descent_of_endpoint
  · rw [data_18_3327.1]; exact data_18_3327.2.2
  · rw [data_18_3327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 3375). -/
theorem data_18_3375 : oddCount 3375 18 = 11 ∧
    acceleratedOrbit 18 3375 = 2282 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_3375 : ∀ j : Fin 18,
    3375 ≤ acceleratedOrbit j.val 3375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_3375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3375) = 177147 * m + 2282 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 3375
  rw [data_18_3375.1, data_18_3375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_3375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3375) < 262144 * m + 3375 := by
  apply descent_of_endpoint
  · rw [data_18_3375.1]; exact data_18_3375.2.2
  · rw [data_18_3375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 3583). -/
theorem data_18_3583 : oddCount 3583 18 = 11 ∧
    acceleratedOrbit 18 3583 = 2422 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_3583 : ∀ j : Fin 18,
    3583 ≤ acceleratedOrbit j.val 3583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_3583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3583) = 177147 * m + 2422 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 3583
  rw [data_18_3583.1, data_18_3583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_3583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3583) < 262144 * m + 3583 := by
  apply descent_of_endpoint
  · rw [data_18_3583.1]; exact data_18_3583.2.2
  · rw [data_18_3583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 3615). -/
theorem data_18_3615 : oddCount 3615 18 = 11 ∧
    acceleratedOrbit 18 3615 = 2444 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_3615 : ∀ j : Fin 18,
    3615 ≤ acceleratedOrbit j.val 3615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_3615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3615) = 177147 * m + 2444 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 3615
  rw [data_18_3615.1, data_18_3615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_3615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3615) < 262144 * m + 3615 := by
  apply descent_of_endpoint
  · rw [data_18_3615.1]; exact data_18_3615.2.2
  · rw [data_18_3615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 3775). -/
theorem data_18_3775 : oddCount 3775 18 = 11 ∧
    acceleratedOrbit 18 3775 = 2552 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_3775 : ∀ j : Fin 18,
    3775 ≤ acceleratedOrbit j.val 3775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_3775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3775) = 177147 * m + 2552 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 3775
  rw [data_18_3775.1, data_18_3775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_3775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3775) < 262144 * m + 3775 := by
  apply descent_of_endpoint
  · rw [data_18_3775.1]; exact data_18_3775.2.2
  · rw [data_18_3775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 4143). -/
theorem data_18_4143 : oddCount 4143 18 = 11 ∧
    acceleratedOrbit 18 4143 = 2801 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_4143 : ∀ j : Fin 18,
    4143 ≤ acceleratedOrbit j.val 4143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_4143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 4143) = 177147 * m + 2801 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 4143
  rw [data_18_4143.1, data_18_4143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_4143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 4143) < 262144 * m + 4143 := by
  apply descent_of_endpoint
  · rw [data_18_4143.1]; exact data_18_4143.2.2
  · rw [data_18_4143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 4543). -/
theorem data_18_4543 : oddCount 4543 18 = 11 ∧
    acceleratedOrbit 18 4543 = 3071 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_4543 : ∀ j : Fin 18,
    4543 ≤ acceleratedOrbit j.val 4543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_4543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 4543) = 177147 * m + 3071 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 4543
  rw [data_18_4543.1, data_18_4543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_4543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 4543) < 262144 * m + 4543 := by
  apply descent_of_endpoint
  · rw [data_18_4543.1]; exact data_18_4543.2.2
  · rw [data_18_4543.2.1]; decide

end Collatz.Research.FirstDescent.Batch101
