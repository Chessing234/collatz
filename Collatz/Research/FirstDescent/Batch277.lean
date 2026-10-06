import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 277. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch277
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 174399). -/
theorem data_20_174399 : oddCount 174399 20 = 12 ∧
    acceleratedOrbit 20 174399 = 88390 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_174399 : ∀ j : Fin 20,
    174399 ≤ acceleratedOrbit j.val 174399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_174399 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 174399) = 531441 * m + 88390 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 174399
  rw [data_20_174399.1, data_20_174399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_174399 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 174399) < 1048576 * m + 174399 := by
  apply descent_of_endpoint
  · rw [data_20_174399.1]; exact data_20_174399.2.2
  · rw [data_20_174399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 174719). -/
theorem data_20_174719 : oddCount 174719 20 = 12 ∧
    acceleratedOrbit 20 174719 = 88552 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_174719 : ∀ j : Fin 20,
    174719 ≤ acceleratedOrbit j.val 174719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_174719 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 174719) = 531441 * m + 88552 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 174719
  rw [data_20_174719.1, data_20_174719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_174719 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 174719) < 1048576 * m + 174719 := by
  apply descent_of_endpoint
  · rw [data_20_174719.1]; exact data_20_174719.2.2
  · rw [data_20_174719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 175135). -/
theorem data_20_175135 : oddCount 175135 20 = 12 ∧
    acceleratedOrbit 20 175135 = 88763 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_175135 : ∀ j : Fin 20,
    175135 ≤ acceleratedOrbit j.val 175135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_175135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 175135) = 531441 * m + 88763 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 175135
  rw [data_20_175135.1, data_20_175135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_175135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 175135) < 1048576 * m + 175135 := by
  apply descent_of_endpoint
  · rw [data_20_175135.1]; exact data_20_175135.2.2
  · rw [data_20_175135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 175259). -/
theorem data_20_175259 : oddCount 175259 20 = 12 ∧
    acceleratedOrbit 20 175259 = 88826 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_175259 : ∀ j : Fin 20,
    175259 ≤ acceleratedOrbit j.val 175259 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_175259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 175259) = 531441 * m + 88826 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 175259
  rw [data_20_175259.1, data_20_175259.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_175259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 175259) < 1048576 * m + 175259 := by
  apply descent_of_endpoint
  · rw [data_20_175259.1]; exact data_20_175259.2.2
  · rw [data_20_175259.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 175963). -/
theorem data_20_175963 : oddCount 175963 20 = 12 ∧
    acceleratedOrbit 20 175963 = 89183 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_175963 : ∀ j : Fin 20,
    175963 ≤ acceleratedOrbit j.val 175963 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_175963 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 175963) = 531441 * m + 89183 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 175963
  rw [data_20_175963.1, data_20_175963.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_175963 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 175963) < 1048576 * m + 175963 := by
  apply descent_of_endpoint
  · rw [data_20_175963.1]; exact data_20_175963.2.2
  · rw [data_20_175963.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 177791). -/
theorem data_20_177791 : oddCount 177791 20 = 12 ∧
    acceleratedOrbit 20 177791 = 90109 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_177791 : ∀ j : Fin 20,
    177791 ≤ acceleratedOrbit j.val 177791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_177791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 177791) = 531441 * m + 90109 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 177791
  rw [data_20_177791.1, data_20_177791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_177791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 177791) < 1048576 * m + 177791 := by
  apply descent_of_endpoint
  · rw [data_20_177791.1]; exact data_20_177791.2.2
  · rw [data_20_177791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 178047). -/
theorem data_20_178047 : oddCount 178047 20 = 12 ∧
    acceleratedOrbit 20 178047 = 90239 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_178047 : ∀ j : Fin 20,
    178047 ≤ acceleratedOrbit j.val 178047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_178047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178047) = 531441 * m + 90239 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 178047
  rw [data_20_178047.1, data_20_178047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_178047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178047) < 1048576 * m + 178047 := by
  apply descent_of_endpoint
  · rw [data_20_178047.1]; exact data_20_178047.2.2
  · rw [data_20_178047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 178207). -/
theorem data_20_178207 : oddCount 178207 20 = 12 ∧
    acceleratedOrbit 20 178207 = 90320 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_178207 : ∀ j : Fin 20,
    178207 ≤ acceleratedOrbit j.val 178207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_178207 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178207) = 531441 * m + 90320 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 178207
  rw [data_20_178207.1, data_20_178207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_178207 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178207) < 1048576 * m + 178207 := by
  apply descent_of_endpoint
  · rw [data_20_178207.1]; exact data_20_178207.2.2
  · rw [data_20_178207.2.1]; decide

end Collatz.Research.FirstDescent.Batch277
