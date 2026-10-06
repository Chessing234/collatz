import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 292. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch292
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 216479). -/
theorem data_20_216479 : oddCount 216479 20 = 12 ∧
    acceleratedOrbit 20 216479 = 109717 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_216479 : ∀ j : Fin 20,
    216479 ≤ acceleratedOrbit j.val 216479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_216479 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216479) = 531441 * m + 109717 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 216479
  rw [data_20_216479.1, data_20_216479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_216479 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216479) < 1048576 * m + 216479 := by
  apply descent_of_endpoint
  · rw [data_20_216479.1]; exact data_20_216479.2.2
  · rw [data_20_216479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 216623). -/
theorem data_20_216623 : oddCount 216623 20 = 12 ∧
    acceleratedOrbit 20 216623 = 109790 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_216623 : ∀ j : Fin 20,
    216623 ≤ acceleratedOrbit j.val 216623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_216623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216623) = 531441 * m + 109790 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 216623
  rw [data_20_216623.1, data_20_216623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_216623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216623) < 1048576 * m + 216623 := by
  apply descent_of_endpoint
  · rw [data_20_216623.1]; exact data_20_216623.2.2
  · rw [data_20_216623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 216935). -/
theorem data_20_216935 : oddCount 216935 20 = 12 ∧
    acceleratedOrbit 20 216935 = 109948 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_216935 : ∀ j : Fin 20,
    216935 ≤ acceleratedOrbit j.val 216935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_216935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216935) = 531441 * m + 109948 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 216935
  rw [data_20_216935.1, data_20_216935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_216935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216935) < 1048576 * m + 216935 := by
  apply descent_of_endpoint
  · rw [data_20_216935.1]; exact data_20_216935.2.2
  · rw [data_20_216935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 216999). -/
theorem data_20_216999 : oddCount 216999 20 = 12 ∧
    acceleratedOrbit 20 216999 = 109981 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_216999 : ∀ j : Fin 20,
    216999 ≤ acceleratedOrbit j.val 216999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_216999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216999) = 531441 * m + 109981 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 216999
  rw [data_20_216999.1, data_20_216999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_216999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216999) < 1048576 * m + 216999 := by
  apply descent_of_endpoint
  · rw [data_20_216999.1]; exact data_20_216999.2.2
  · rw [data_20_216999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 217159). -/
theorem data_20_217159 : oddCount 217159 20 = 12 ∧
    acceleratedOrbit 20 217159 = 110062 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_217159 : ∀ j : Fin 20,
    217159 ≤ acceleratedOrbit j.val 217159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_217159 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 217159) = 531441 * m + 110062 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 217159
  rw [data_20_217159.1, data_20_217159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_217159 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 217159) < 1048576 * m + 217159 := by
  apply descent_of_endpoint
  · rw [data_20_217159.1]; exact data_20_217159.2.2
  · rw [data_20_217159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 218215). -/
theorem data_20_218215 : oddCount 218215 20 = 12 ∧
    acceleratedOrbit 20 218215 = 110597 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_218215 : ∀ j : Fin 20,
    218215 ≤ acceleratedOrbit j.val 218215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_218215 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 218215) = 531441 * m + 110597 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 218215
  rw [data_20_218215.1, data_20_218215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_218215 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 218215) < 1048576 * m + 218215 := by
  apply descent_of_endpoint
  · rw [data_20_218215.1]; exact data_20_218215.2.2
  · rw [data_20_218215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 218559). -/
theorem data_20_218559 : oddCount 218559 20 = 12 ∧
    acceleratedOrbit 20 218559 = 110771 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_218559 : ∀ j : Fin 20,
    218559 ≤ acceleratedOrbit j.val 218559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_218559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 218559) = 531441 * m + 110771 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 218559
  rw [data_20_218559.1, data_20_218559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_218559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 218559) < 1048576 * m + 218559 := by
  apply descent_of_endpoint
  · rw [data_20_218559.1]; exact data_20_218559.2.2
  · rw [data_20_218559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 218983). -/
theorem data_20_218983 : oddCount 218983 20 = 12 ∧
    acceleratedOrbit 20 218983 = 110986 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_218983 : ∀ j : Fin 20,
    218983 ≤ acceleratedOrbit j.val 218983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_218983 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 218983) = 531441 * m + 110986 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 218983
  rw [data_20_218983.1, data_20_218983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_218983 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 218983) < 1048576 * m + 218983 := by
  apply descent_of_endpoint
  · rw [data_20_218983.1]; exact data_20_218983.2.2
  · rw [data_20_218983.2.1]; decide

end Collatz.Research.FirstDescent.Batch292
