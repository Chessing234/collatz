import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 294. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch294
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 222055). -/
theorem data_20_222055 : oddCount 222055 20 = 12 ∧
    acceleratedOrbit 20 222055 = 112543 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_222055 : ∀ j : Fin 20,
    222055 ≤ acceleratedOrbit j.val 222055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_222055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222055) = 531441 * m + 112543 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 222055
  rw [data_20_222055.1, data_20_222055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_222055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222055) < 1048576 * m + 222055 := by
  apply descent_of_endpoint
  · rw [data_20_222055.1]; exact data_20_222055.2.2
  · rw [data_20_222055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 222175). -/
theorem data_20_222175 : oddCount 222175 20 = 12 ∧
    acceleratedOrbit 20 222175 = 112604 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_222175 : ∀ j : Fin 20,
    222175 ≤ acceleratedOrbit j.val 222175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_222175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222175) = 531441 * m + 112604 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 222175
  rw [data_20_222175.1, data_20_222175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_222175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222175) < 1048576 * m + 222175 := by
  apply descent_of_endpoint
  · rw [data_20_222175.1]; exact data_20_222175.2.2
  · rw [data_20_222175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 222335). -/
theorem data_20_222335 : oddCount 222335 20 = 12 ∧
    acceleratedOrbit 20 222335 = 112685 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_222335 : ∀ j : Fin 20,
    222335 ≤ acceleratedOrbit j.val 222335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_222335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222335) = 531441 * m + 112685 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 222335
  rw [data_20_222335.1, data_20_222335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_222335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222335) < 1048576 * m + 222335 := by
  apply descent_of_endpoint
  · rw [data_20_222335.1]; exact data_20_222335.2.2
  · rw [data_20_222335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 223303). -/
theorem data_20_223303 : oddCount 223303 20 = 12 ∧
    acceleratedOrbit 20 223303 = 113176 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_223303 : ∀ j : Fin 20,
    223303 ≤ acceleratedOrbit j.val 223303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_223303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 223303) = 531441 * m + 113176 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 223303
  rw [data_20_223303.1, data_20_223303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_223303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 223303) < 1048576 * m + 223303 := by
  apply descent_of_endpoint
  · rw [data_20_223303.1]; exact data_20_223303.2.2
  · rw [data_20_223303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 223463). -/
theorem data_20_223463 : oddCount 223463 20 = 12 ∧
    acceleratedOrbit 20 223463 = 113257 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_223463 : ∀ j : Fin 20,
    223463 ≤ acceleratedOrbit j.val 223463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_223463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 223463) = 531441 * m + 113257 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 223463
  rw [data_20_223463.1, data_20_223463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_223463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 223463) < 1048576 * m + 223463 := by
  apply descent_of_endpoint
  · rw [data_20_223463.1]; exact data_20_223463.2.2
  · rw [data_20_223463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 224103). -/
theorem data_20_224103 : oddCount 224103 20 = 12 ∧
    acceleratedOrbit 20 224103 = 113581 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_224103 : ∀ j : Fin 20,
    224103 ≤ acceleratedOrbit j.val 224103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_224103 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224103) = 531441 * m + 113581 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 224103
  rw [data_20_224103.1, data_20_224103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_224103 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224103) < 1048576 * m + 224103 := by
  apply descent_of_endpoint
  · rw [data_20_224103.1]; exact data_20_224103.2.2
  · rw [data_20_224103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 224127). -/
theorem data_20_224127 : oddCount 224127 20 = 12 ∧
    acceleratedOrbit 20 224127 = 113593 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_224127 : ∀ j : Fin 20,
    224127 ≤ acceleratedOrbit j.val 224127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_224127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224127) = 531441 * m + 113593 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 224127
  rw [data_20_224127.1, data_20_224127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_224127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224127) < 1048576 * m + 224127 := by
  apply descent_of_endpoint
  · rw [data_20_224127.1]; exact data_20_224127.2.2
  · rw [data_20_224127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 224239). -/
theorem data_20_224239 : oddCount 224239 20 = 12 ∧
    acceleratedOrbit 20 224239 = 113650 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_224239 : ∀ j : Fin 20,
    224239 ≤ acceleratedOrbit j.val 224239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_224239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224239) = 531441 * m + 113650 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 224239
  rw [data_20_224239.1, data_20_224239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_224239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224239) < 1048576 * m + 224239 := by
  apply descent_of_endpoint
  · rw [data_20_224239.1]; exact data_20_224239.2.2
  · rw [data_20_224239.2.1]; decide

end Collatz.Research.FirstDescent.Batch294
