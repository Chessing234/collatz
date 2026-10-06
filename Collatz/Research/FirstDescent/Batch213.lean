import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 213. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch213
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 247263). -/
theorem data_18_247263 : oddCount 247263 18 = 11 ∧
    acceleratedOrbit 18 247263 = 167092 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_247263 : ∀ j : Fin 18,
    247263 ≤ acceleratedOrbit j.val 247263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_247263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247263) = 177147 * m + 167092 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 247263
  rw [data_18_247263.1, data_18_247263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_247263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247263) < 262144 * m + 247263 := by
  apply descent_of_endpoint
  · rw [data_18_247263.1]; exact data_18_247263.2.2
  · rw [data_18_247263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 247343). -/
theorem data_18_247343 : oddCount 247343 18 = 11 ∧
    acceleratedOrbit 18 247343 = 167146 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_247343 : ∀ j : Fin 18,
    247343 ≤ acceleratedOrbit j.val 247343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_247343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247343) = 177147 * m + 167146 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 247343
  rw [data_18_247343.1, data_18_247343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_247343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247343) < 262144 * m + 247343 := by
  apply descent_of_endpoint
  · rw [data_18_247343.1]; exact data_18_247343.2.2
  · rw [data_18_247343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 247535). -/
theorem data_18_247535 : oddCount 247535 18 = 11 ∧
    acceleratedOrbit 18 247535 = 167276 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_247535 : ∀ j : Fin 18,
    247535 ≤ acceleratedOrbit j.val 247535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_247535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247535) = 177147 * m + 167276 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 247535
  rw [data_18_247535.1, data_18_247535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_247535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247535) < 262144 * m + 247535 := by
  apply descent_of_endpoint
  · rw [data_18_247535.1]; exact data_18_247535.2.2
  · rw [data_18_247535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 247899). -/
theorem data_18_247899 : oddCount 247899 18 = 11 ∧
    acceleratedOrbit 18 247899 = 167522 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_247899 : ∀ j : Fin 18,
    247899 ≤ acceleratedOrbit j.val 247899 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_247899 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247899) = 177147 * m + 167522 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 247899
  rw [data_18_247899.1, data_18_247899.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_247899 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247899) < 262144 * m + 247899 := by
  apply descent_of_endpoint
  · rw [data_18_247899.1]; exact data_18_247899.2.2
  · rw [data_18_247899.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 247935). -/
theorem data_18_247935 : oddCount 247935 18 = 11 ∧
    acceleratedOrbit 18 247935 = 167546 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_247935 : ∀ j : Fin 18,
    247935 ≤ acceleratedOrbit j.val 247935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_247935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247935) = 177147 * m + 167546 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 247935
  rw [data_18_247935.1, data_18_247935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_247935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 247935) < 262144 * m + 247935 := by
  apply descent_of_endpoint
  · rw [data_18_247935.1]; exact data_18_247935.2.2
  · rw [data_18_247935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 249391). -/
theorem data_18_249391 : oddCount 249391 18 = 11 ∧
    acceleratedOrbit 18 249391 = 168530 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_249391 : ∀ j : Fin 18,
    249391 ≤ acceleratedOrbit j.val 249391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_249391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 249391) = 177147 * m + 168530 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 249391
  rw [data_18_249391.1, data_18_249391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_249391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 249391) < 262144 * m + 249391 := by
  apply descent_of_endpoint
  · rw [data_18_249391.1]; exact data_18_249391.2.2
  · rw [data_18_249391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 250459). -/
theorem data_18_250459 : oddCount 250459 18 = 11 ∧
    acceleratedOrbit 18 250459 = 169252 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_250459 : ∀ j : Fin 18,
    250459 ≤ acceleratedOrbit j.val 250459 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_250459 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 250459) = 177147 * m + 169252 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 250459
  rw [data_18_250459.1, data_18_250459.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_250459 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 250459) < 262144 * m + 250459 := by
  apply descent_of_endpoint
  · rw [data_18_250459.1]; exact data_18_250459.2.2
  · rw [data_18_250459.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 250971). -/
theorem data_18_250971 : oddCount 250971 18 = 11 ∧
    acceleratedOrbit 18 250971 = 169598 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_250971 : ∀ j : Fin 18,
    250971 ≤ acceleratedOrbit j.val 250971 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_250971 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 250971) = 177147 * m + 169598 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 250971
  rw [data_18_250971.1, data_18_250971.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_250971 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 250971) < 262144 * m + 250971 := by
  apply descent_of_endpoint
  · rw [data_18_250971.1]; exact data_18_250971.2.2
  · rw [data_18_250971.2.1]; decide

end Collatz.Research.FirstDescent.Batch213
