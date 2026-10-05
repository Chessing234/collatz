import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 296. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch296
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 226863). -/
theorem data_20_226863 : oddCount 226863 20 = 12 ∧
    acceleratedOrbit 20 226863 = 114980 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_226863 : ∀ j : Fin 20,
    226863 ≤ acceleratedOrbit j.val 226863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_226863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 226863) = 531441 * m + 114980 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 226863
  rw [data_20_226863.1, data_20_226863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_226863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 226863) < 1048576 * m + 226863 := by
  apply descent_of_endpoint
  · rw [data_20_226863.1]; exact data_20_226863.2.2
  · rw [data_20_226863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 227175). -/
theorem data_20_227175 : oddCount 227175 20 = 12 ∧
    acceleratedOrbit 20 227175 = 115138 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_227175 : ∀ j : Fin 20,
    227175 ≤ acceleratedOrbit j.val 227175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_227175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 227175) = 531441 * m + 115138 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 227175
  rw [data_20_227175.1, data_20_227175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_227175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 227175) < 1048576 * m + 227175 := by
  apply descent_of_endpoint
  · rw [data_20_227175.1]; exact data_20_227175.2.2
  · rw [data_20_227175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 227431). -/
theorem data_20_227431 : oddCount 227431 20 = 12 ∧
    acceleratedOrbit 20 227431 = 115268 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_227431 : ∀ j : Fin 20,
    227431 ≤ acceleratedOrbit j.val 227431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_227431 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 227431) = 531441 * m + 115268 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 227431
  rw [data_20_227431.1, data_20_227431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_227431 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 227431) < 1048576 * m + 227431 := by
  apply descent_of_endpoint
  · rw [data_20_227431.1]; exact data_20_227431.2.2
  · rw [data_20_227431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 228199). -/
theorem data_20_228199 : oddCount 228199 20 = 12 ∧
    acceleratedOrbit 20 228199 = 115657 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_228199 : ∀ j : Fin 20,
    228199 ≤ acceleratedOrbit j.val 228199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_228199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 228199) = 531441 * m + 115657 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 228199
  rw [data_20_228199.1, data_20_228199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_228199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 228199) < 1048576 * m + 228199 := by
  apply descent_of_endpoint
  · rw [data_20_228199.1]; exact data_20_228199.2.2
  · rw [data_20_228199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 228223). -/
theorem data_20_228223 : oddCount 228223 20 = 12 ∧
    acceleratedOrbit 20 228223 = 115669 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_228223 : ∀ j : Fin 20,
    228223 ≤ acceleratedOrbit j.val 228223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_228223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 228223) = 531441 * m + 115669 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 228223
  rw [data_20_228223.1, data_20_228223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_228223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 228223) < 1048576 * m + 228223 := by
  apply descent_of_endpoint
  · rw [data_20_228223.1]; exact data_20_228223.2.2
  · rw [data_20_228223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 228603). -/
theorem data_20_228603 : oddCount 228603 20 = 12 ∧
    acceleratedOrbit 20 228603 = 115862 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_228603 : ∀ j : Fin 20,
    228603 ≤ acceleratedOrbit j.val 228603 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_228603 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 228603) = 531441 * m + 115862 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 228603
  rw [data_20_228603.1, data_20_228603.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_228603 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 228603) < 1048576 * m + 228603 := by
  apply descent_of_endpoint
  · rw [data_20_228603.1]; exact data_20_228603.2.2
  · rw [data_20_228603.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 229627). -/
theorem data_20_229627 : oddCount 229627 20 = 12 ∧
    acceleratedOrbit 20 229627 = 116381 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_229627 : ∀ j : Fin 20,
    229627 ≤ acceleratedOrbit j.val 229627 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_229627 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 229627) = 531441 * m + 116381 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 229627
  rw [data_20_229627.1, data_20_229627.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_229627 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 229627) < 1048576 * m + 229627 := by
  apply descent_of_endpoint
  · rw [data_20_229627.1]; exact data_20_229627.2.2
  · rw [data_20_229627.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 229823). -/
theorem data_20_229823 : oddCount 229823 20 = 12 ∧
    acceleratedOrbit 20 229823 = 116480 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_229823 : ∀ j : Fin 20,
    229823 ≤ acceleratedOrbit j.val 229823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_229823 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 229823) = 531441 * m + 116480 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 229823
  rw [data_20_229823.1, data_20_229823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_229823 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 229823) < 1048576 * m + 229823 := by
  apply descent_of_endpoint
  · rw [data_20_229823.1]; exact data_20_229823.2.2
  · rw [data_20_229823.2.1]; decide

end Collatz.Research.FirstDescent.Batch296
