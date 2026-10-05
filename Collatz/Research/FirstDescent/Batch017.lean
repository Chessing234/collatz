import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 17. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch017
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7079). -/
theorem data_13_7079 : oddCount 7079 13 = 8 ∧
    acceleratedOrbit 13 7079 = 5671 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7079 : ∀ j : Fin 13,
    7079 ≤ acceleratedOrbit j.val 7079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7079 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7079) = 6561 * m + 5671 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7079
  rw [data_13_7079.1, data_13_7079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7079 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7079) < 8192 * m + 7079 := by
  apply descent_of_endpoint
  · rw [data_13_7079.1]; exact data_13_7079.2.2
  · rw [data_13_7079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7259). -/
theorem data_13_7259 : oddCount 7259 13 = 8 ∧
    acceleratedOrbit 13 7259 = 5815 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7259 : ∀ j : Fin 13,
    7259 ≤ acceleratedOrbit j.val 7259 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7259 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7259) = 6561 * m + 5815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7259
  rw [data_13_7259.1, data_13_7259.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7259 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7259) < 8192 * m + 7259 := by
  apply descent_of_endpoint
  · rw [data_13_7259.1]; exact data_13_7259.2.2
  · rw [data_13_7259.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7375). -/
theorem data_13_7375 : oddCount 7375 13 = 8 ∧
    acceleratedOrbit 13 7375 = 5908 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7375 : ∀ j : Fin 13,
    7375 ≤ acceleratedOrbit j.val 7375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7375 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7375) = 6561 * m + 5908 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7375
  rw [data_13_7375.1, data_13_7375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7375 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7375) < 8192 * m + 7375 := by
  apply descent_of_endpoint
  · rw [data_13_7375.1]; exact data_13_7375.2.2
  · rw [data_13_7375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7399). -/
theorem data_13_7399 : oddCount 7399 13 = 8 ∧
    acceleratedOrbit 13 7399 = 5927 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7399 : ∀ j : Fin 13,
    7399 ≤ acceleratedOrbit j.val 7399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7399 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7399) = 6561 * m + 5927 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7399
  rw [data_13_7399.1, data_13_7399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7399 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7399) < 8192 * m + 7399 := by
  apply descent_of_endpoint
  · rw [data_13_7399.1]; exact data_13_7399.2.2
  · rw [data_13_7399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7495). -/
theorem data_13_7495 : oddCount 7495 13 = 8 ∧
    acceleratedOrbit 13 7495 = 6004 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7495 : ∀ j : Fin 13,
    7495 ≤ acceleratedOrbit j.val 7495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7495 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7495) = 6561 * m + 6004 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7495
  rw [data_13_7495.1, data_13_7495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7495 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7495) < 8192 * m + 7495 := by
  apply descent_of_endpoint
  · rw [data_13_7495.1]; exact data_13_7495.2.2
  · rw [data_13_7495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7631). -/
theorem data_13_7631 : oddCount 7631 13 = 8 ∧
    acceleratedOrbit 13 7631 = 6113 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7631 : ∀ j : Fin 13,
    7631 ≤ acceleratedOrbit j.val 7631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7631 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7631) = 6561 * m + 6113 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7631
  rw [data_13_7631.1, data_13_7631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7631 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7631) < 8192 * m + 7631 := by
  apply descent_of_endpoint
  · rw [data_13_7631.1]; exact data_13_7631.2.2
  · rw [data_13_7631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7791). -/
theorem data_13_7791 : oddCount 7791 13 = 8 ∧
    acceleratedOrbit 13 7791 = 6241 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7791 : ∀ j : Fin 13,
    7791 ≤ acceleratedOrbit j.val 7791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7791 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7791) = 6561 * m + 6241 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7791
  rw [data_13_7791.1, data_13_7791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7791 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7791) < 8192 * m + 7791 := by
  apply descent_of_endpoint
  · rw [data_13_7791.1]; exact data_13_7791.2.2
  · rw [data_13_7791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7847). -/
theorem data_13_7847 : oddCount 7847 13 = 8 ∧
    acceleratedOrbit 13 7847 = 6286 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7847 : ∀ j : Fin 13,
    7847 ≤ acceleratedOrbit j.val 7847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7847 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7847) = 6561 * m + 6286 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7847
  rw [data_13_7847.1, data_13_7847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7847 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7847) < 8192 * m + 7847 := by
  apply descent_of_endpoint
  · rw [data_13_7847.1]; exact data_13_7847.2.2
  · rw [data_13_7847.2.1]; decide

end Collatz.Research.FirstDescent.Batch017
