import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 214. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch214
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 251263). -/
theorem data_18_251263 : oddCount 251263 18 = 11 ∧
    acceleratedOrbit 18 251263 = 169795 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_251263 : ∀ j : Fin 18,
    251263 ≤ acceleratedOrbit j.val 251263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_251263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251263) = 177147 * m + 169795 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 251263
  rw [data_18_251263.1, data_18_251263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_251263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251263) < 262144 * m + 251263 := by
  apply descent_of_endpoint
  · rw [data_18_251263.1]; exact data_18_251263.2.2
  · rw [data_18_251263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 251327). -/
theorem data_18_251327 : oddCount 251327 18 = 11 ∧
    acceleratedOrbit 18 251327 = 169838 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_251327 : ∀ j : Fin 18,
    251327 ≤ acceleratedOrbit j.val 251327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_251327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251327) = 177147 * m + 169838 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 251327
  rw [data_18_251327.1, data_18_251327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_251327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251327) < 262144 * m + 251327 := by
  apply descent_of_endpoint
  · rw [data_18_251327.1]; exact data_18_251327.2.2
  · rw [data_18_251327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 251495). -/
theorem data_18_251495 : oddCount 251495 18 = 11 ∧
    acceleratedOrbit 18 251495 = 169952 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_251495 : ∀ j : Fin 18,
    251495 ≤ acceleratedOrbit j.val 251495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_251495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251495) = 177147 * m + 169952 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 251495
  rw [data_18_251495.1, data_18_251495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_251495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251495) < 262144 * m + 251495 := by
  apply descent_of_endpoint
  · rw [data_18_251495.1]; exact data_18_251495.2.2
  · rw [data_18_251495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 251775). -/
theorem data_18_251775 : oddCount 251775 18 = 11 ∧
    acceleratedOrbit 18 251775 = 170141 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_251775 : ∀ j : Fin 18,
    251775 ≤ acceleratedOrbit j.val 251775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_251775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251775) = 177147 * m + 170141 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 251775
  rw [data_18_251775.1, data_18_251775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_251775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 251775) < 262144 * m + 251775 := by
  apply descent_of_endpoint
  · rw [data_18_251775.1]; exact data_18_251775.2.2
  · rw [data_18_251775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 252263). -/
theorem data_18_252263 : oddCount 252263 18 = 11 ∧
    acceleratedOrbit 18 252263 = 170471 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_252263 : ∀ j : Fin 18,
    252263 ≤ acceleratedOrbit j.val 252263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_252263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 252263) = 177147 * m + 170471 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 252263
  rw [data_18_252263.1, data_18_252263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_252263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 252263) < 262144 * m + 252263 := by
  apply descent_of_endpoint
  · rw [data_18_252263.1]; exact data_18_252263.2.2
  · rw [data_18_252263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 252351). -/
theorem data_18_252351 : oddCount 252351 18 = 11 ∧
    acceleratedOrbit 18 252351 = 170530 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_252351 : ∀ j : Fin 18,
    252351 ≤ acceleratedOrbit j.val 252351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_252351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 252351) = 177147 * m + 170530 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 252351
  rw [data_18_252351.1, data_18_252351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_252351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 252351) < 262144 * m + 252351 := by
  apply descent_of_endpoint
  · rw [data_18_252351.1]; exact data_18_252351.2.2
  · rw [data_18_252351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 252543). -/
theorem data_18_252543 : oddCount 252543 18 = 11 ∧
    acceleratedOrbit 18 252543 = 170660 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_252543 : ∀ j : Fin 18,
    252543 ≤ acceleratedOrbit j.val 252543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_252543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 252543) = 177147 * m + 170660 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 252543
  rw [data_18_252543.1, data_18_252543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_252543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 252543) < 262144 * m + 252543 := by
  apply descent_of_endpoint
  · rw [data_18_252543.1]; exact data_18_252543.2.2
  · rw [data_18_252543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 253407). -/
theorem data_18_253407 : oddCount 253407 18 = 11 ∧
    acceleratedOrbit 18 253407 = 171244 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_253407 : ∀ j : Fin 18,
    253407 ≤ acceleratedOrbit j.val 253407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_253407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253407) = 177147 * m + 171244 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 253407
  rw [data_18_253407.1, data_18_253407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_253407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253407) < 262144 * m + 253407 := by
  apply descent_of_endpoint
  · rw [data_18_253407.1]; exact data_18_253407.2.2
  · rw [data_18_253407.2.1]; decide

end Collatz.Research.FirstDescent.Batch214
