import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 222. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch222
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 5211). -/
theorem data_20_5211 : oddCount 5211 20 = 12 ∧
    acceleratedOrbit 20 5211 = 2642 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_5211 : ∀ j : Fin 20,
    5211 ≤ acceleratedOrbit j.val 5211 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_5211 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5211) = 531441 * m + 2642 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 5211
  rw [data_20_5211.1, data_20_5211.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_5211 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5211) < 1048576 * m + 5211 := by
  apply descent_of_endpoint
  · rw [data_20_5211.1]; exact data_20_5211.2.2
  · rw [data_20_5211.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 5223). -/
theorem data_20_5223 : oddCount 5223 20 = 12 ∧
    acceleratedOrbit 20 5223 = 2648 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_5223 : ∀ j : Fin 20,
    5223 ≤ acceleratedOrbit j.val 5223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_5223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5223) = 531441 * m + 2648 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 5223
  rw [data_20_5223.1, data_20_5223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_5223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5223) < 1048576 * m + 5223 := by
  apply descent_of_endpoint
  · rw [data_20_5223.1]; exact data_20_5223.2.2
  · rw [data_20_5223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 5247). -/
theorem data_20_5247 : oddCount 5247 20 = 12 ∧
    acceleratedOrbit 20 5247 = 2660 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_5247 : ∀ j : Fin 20,
    5247 ≤ acceleratedOrbit j.val 5247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_5247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5247) = 531441 * m + 2660 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 5247
  rw [data_20_5247.1, data_20_5247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_5247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5247) < 1048576 * m + 5247 := by
  apply descent_of_endpoint
  · rw [data_20_5247.1]; exact data_20_5247.2.2
  · rw [data_20_5247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 5679). -/
theorem data_20_5679 : oddCount 5679 20 = 12 ∧
    acceleratedOrbit 20 5679 = 2879 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_5679 : ∀ j : Fin 20,
    5679 ≤ acceleratedOrbit j.val 5679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_5679 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5679) = 531441 * m + 2879 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 5679
  rw [data_20_5679.1, data_20_5679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_5679 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 5679) < 1048576 * m + 5679 := by
  apply descent_of_endpoint
  · rw [data_20_5679.1]; exact data_20_5679.2.2
  · rw [data_20_5679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 6235). -/
theorem data_20_6235 : oddCount 6235 20 = 12 ∧
    acceleratedOrbit 20 6235 = 3161 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_6235 : ∀ j : Fin 20,
    6235 ≤ acceleratedOrbit j.val 6235 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_6235 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 6235) = 531441 * m + 3161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 6235
  rw [data_20_6235.1, data_20_6235.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_6235 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 6235) < 1048576 * m + 6235 := by
  apply descent_of_endpoint
  · rw [data_20_6235.1]; exact data_20_6235.2.2
  · rw [data_20_6235.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 7271). -/
theorem data_20_7271 : oddCount 7271 20 = 12 ∧
    acceleratedOrbit 20 7271 = 3686 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_7271 : ∀ j : Fin 20,
    7271 ≤ acceleratedOrbit j.val 7271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_7271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7271) = 531441 * m + 3686 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 7271
  rw [data_20_7271.1, data_20_7271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_7271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7271) < 1048576 * m + 7271 := by
  apply descent_of_endpoint
  · rw [data_20_7271.1]; exact data_20_7271.2.2
  · rw [data_20_7271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 7583). -/
theorem data_20_7583 : oddCount 7583 20 = 12 ∧
    acceleratedOrbit 20 7583 = 3844 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_7583 : ∀ j : Fin 20,
    7583 ≤ acceleratedOrbit j.val 7583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_7583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7583) = 531441 * m + 3844 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 7583
  rw [data_20_7583.1, data_20_7583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_7583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7583) < 1048576 * m + 7583 := by
  apply descent_of_endpoint
  · rw [data_20_7583.1]; exact data_20_7583.2.2
  · rw [data_20_7583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 7615). -/
theorem data_20_7615 : oddCount 7615 20 = 12 ∧
    acceleratedOrbit 20 7615 = 3860 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_7615 : ∀ j : Fin 20,
    7615 ≤ acceleratedOrbit j.val 7615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_7615 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7615) = 531441 * m + 3860 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 7615
  rw [data_20_7615.1, data_20_7615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_7615 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 7615) < 1048576 * m + 7615 := by
  apply descent_of_endpoint
  · rw [data_20_7615.1]; exact data_20_7615.2.2
  · rw [data_20_7615.2.1]; decide

end Collatz.Research.FirstDescent.Batch222
