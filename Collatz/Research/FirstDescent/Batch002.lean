import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 2. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch002
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (8, 95). -/
theorem data_8_95 : oddCount 95 8 = 5 ∧
    acceleratedOrbit 8 95 = 91 ∧ 243 < 256 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_8_95 : ∀ j : Fin 8,
    95 ≤ acceleratedOrbit j.val 95 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_8_95 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 95) = 243 * m + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 m 95
  rw [data_8_95.1, data_8_95.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_8_95 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 95) < 256 * m + 95 := by
  apply descent_of_endpoint
  · rw [data_8_95.1]; exact data_8_95.2.2
  · rw [data_8_95.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (8, 123). -/
theorem data_8_123 : oddCount 123 8 = 5 ∧
    acceleratedOrbit 8 123 = 118 ∧ 243 < 256 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_8_123 : ∀ j : Fin 8,
    123 ≤ acceleratedOrbit j.val 123 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_8_123 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 123) = 243 * m + 118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 m 123
  rw [data_8_123.1, data_8_123.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_8_123 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 123) < 256 * m + 123 := by
  apply descent_of_endpoint
  · rw [data_8_123.1]; exact data_8_123.2.2
  · rw [data_8_123.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (8, 175). -/
theorem data_8_175 : oddCount 175 8 = 5 ∧
    acceleratedOrbit 8 175 = 167 ∧ 243 < 256 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_8_175 : ∀ j : Fin 8,
    175 ≤ acceleratedOrbit j.val 175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_8_175 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 175) = 243 * m + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 m 175
  rw [data_8_175.1, data_8_175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_8_175 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 175) < 256 * m + 175 := by
  apply descent_of_endpoint
  · rw [data_8_175.1]; exact data_8_175.2.2
  · rw [data_8_175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (8, 199). -/
theorem data_8_199 : oddCount 199 8 = 5 ∧
    acceleratedOrbit 8 199 = 190 ∧ 243 < 256 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_8_199 : ∀ j : Fin 8,
    199 ≤ acceleratedOrbit j.val 199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_8_199 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 199) = 243 * m + 190 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 m 199
  rw [data_8_199.1, data_8_199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_8_199 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 199) < 256 * m + 199 := by
  apply descent_of_endpoint
  · rw [data_8_199.1]; exact data_8_199.2.2
  · rw [data_8_199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (8, 219). -/
theorem data_8_219 : oddCount 219 8 = 5 ∧
    acceleratedOrbit 8 219 = 209 ∧ 243 < 256 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_8_219 : ∀ j : Fin 8,
    219 ≤ acceleratedOrbit j.val 219 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_8_219 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 219) = 243 * m + 209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 m 219
  rw [data_8_219.1, data_8_219.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_8_219 (m : Nat) :
    acceleratedOrbit 8 (256 * m + 219) < 256 * m + 219 := by
  apply descent_of_endpoint
  · rw [data_8_219.1]; exact data_8_219.2.2
  · rw [data_8_219.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 287). -/
theorem data_10_287 : oddCount 287 10 = 6 ∧
    acceleratedOrbit 10 287 = 205 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_287 : ∀ j : Fin 10,
    287 ≤ acceleratedOrbit j.val 287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_287 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 287) = 729 * m + 205 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 287
  rw [data_10_287.1, data_10_287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_287 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 287) < 1024 * m + 287 := by
  apply descent_of_endpoint
  · rw [data_10_287.1]; exact data_10_287.2.2
  · rw [data_10_287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 347). -/
theorem data_10_347 : oddCount 347 10 = 6 ∧
    acceleratedOrbit 10 347 = 248 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_347 : ∀ j : Fin 10,
    347 ≤ acceleratedOrbit j.val 347 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_347 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 347) = 729 * m + 248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 347
  rw [data_10_347.1, data_10_347.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_347 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 347) < 1024 * m + 347 := by
  apply descent_of_endpoint
  · rw [data_10_347.1]; exact data_10_347.2.2
  · rw [data_10_347.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 367). -/
theorem data_10_367 : oddCount 367 10 = 6 ∧
    acceleratedOrbit 10 367 = 262 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_367 : ∀ j : Fin 10,
    367 ≤ acceleratedOrbit j.val 367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_367 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 367) = 729 * m + 262 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 367
  rw [data_10_367.1, data_10_367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_367 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 367) < 1024 * m + 367 := by
  apply descent_of_endpoint
  · rw [data_10_367.1]; exact data_10_367.2.2
  · rw [data_10_367.2.1]; decide

end Collatz.Research.FirstDescent.Batch002
