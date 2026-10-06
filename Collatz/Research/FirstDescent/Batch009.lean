import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 9. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch009
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 799). -/
theorem data_13_799 : oddCount 799 13 = 8 ∧
    acceleratedOrbit 13 799 = 641 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_799 : ∀ j : Fin 13,
    799 ≤ acceleratedOrbit j.val 799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_799 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 799) = 6561 * m + 641 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 799
  rw [data_13_799.1, data_13_799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_799 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 799) < 8192 * m + 799 := by
  apply descent_of_endpoint
  · rw [data_13_799.1]; exact data_13_799.2.2
  · rw [data_13_799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1071). -/
theorem data_13_1071 : oddCount 1071 13 = 8 ∧
    acceleratedOrbit 13 1071 = 859 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1071 : ∀ j : Fin 13,
    1071 ≤ acceleratedOrbit j.val 1071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1071 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1071) = 6561 * m + 859 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1071
  rw [data_13_1071.1, data_13_1071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1071 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1071) < 8192 * m + 1071 := by
  apply descent_of_endpoint
  · rw [data_13_1071.1]; exact data_13_1071.2.2
  · rw [data_13_1071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1135). -/
theorem data_13_1135 : oddCount 1135 13 = 8 ∧
    acceleratedOrbit 13 1135 = 910 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1135 : ∀ j : Fin 13,
    1135 ≤ acceleratedOrbit j.val 1135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1135 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1135) = 6561 * m + 910 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1135
  rw [data_13_1135.1, data_13_1135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1135 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1135) < 8192 * m + 1135 := by
  apply descent_of_endpoint
  · rw [data_13_1135.1]; exact data_13_1135.2.2
  · rw [data_13_1135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1191). -/
theorem data_13_1191 : oddCount 1191 13 = 8 ∧
    acceleratedOrbit 13 1191 = 955 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1191 : ∀ j : Fin 13,
    1191 ≤ acceleratedOrbit j.val 1191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1191 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1191) = 6561 * m + 955 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1191
  rw [data_13_1191.1, data_13_1191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1191 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1191) < 8192 * m + 1191 := by
  apply descent_of_endpoint
  · rw [data_13_1191.1]; exact data_13_1191.2.2
  · rw [data_13_1191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1215). -/
theorem data_13_1215 : oddCount 1215 13 = 8 ∧
    acceleratedOrbit 13 1215 = 974 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1215 : ∀ j : Fin 13,
    1215 ≤ acceleratedOrbit j.val 1215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1215 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1215) = 6561 * m + 974 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1215
  rw [data_13_1215.1, data_13_1215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1215 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1215) < 8192 * m + 1215 := by
  apply descent_of_endpoint
  · rw [data_13_1215.1]; exact data_13_1215.2.2
  · rw [data_13_1215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1247). -/
theorem data_13_1247 : oddCount 1247 13 = 8 ∧
    acceleratedOrbit 13 1247 = 1000 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1247 : ∀ j : Fin 13,
    1247 ≤ acceleratedOrbit j.val 1247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1247 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1247) = 6561 * m + 1000 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1247
  rw [data_13_1247.1, data_13_1247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1247 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1247) < 8192 * m + 1247 := by
  apply descent_of_endpoint
  · rw [data_13_1247.1]; exact data_13_1247.2.2
  · rw [data_13_1247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1327). -/
theorem data_13_1327 : oddCount 1327 13 = 8 ∧
    acceleratedOrbit 13 1327 = 1064 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1327 : ∀ j : Fin 13,
    1327 ≤ acceleratedOrbit j.val 1327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1327 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1327) = 6561 * m + 1064 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1327
  rw [data_13_1327.1, data_13_1327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1327 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1327) < 8192 * m + 1327 := by
  apply descent_of_endpoint
  · rw [data_13_1327.1]; exact data_13_1327.2.2
  · rw [data_13_1327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 1563). -/
theorem data_13_1563 : oddCount 1563 13 = 8 ∧
    acceleratedOrbit 13 1563 = 1253 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_1563 : ∀ j : Fin 13,
    1563 ≤ acceleratedOrbit j.val 1563 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_1563 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1563) = 6561 * m + 1253 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 1563
  rw [data_13_1563.1, data_13_1563.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_1563 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 1563) < 8192 * m + 1563 := by
  apply descent_of_endpoint
  · rw [data_13_1563.1]; exact data_13_1563.2.2
  · rw [data_13_1563.2.1]; decide

end Collatz.Research.FirstDescent.Batch009
