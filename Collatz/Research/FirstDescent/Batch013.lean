import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 13. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch013
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4159). -/
theorem data_13_4159 : oddCount 4159 13 = 8 ∧
    acceleratedOrbit 13 4159 = 3332 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4159 : ∀ j : Fin 13,
    4159 ≤ acceleratedOrbit j.val 4159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4159 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4159) = 6561 * m + 3332 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4159
  rw [data_13_4159.1, data_13_4159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4159 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4159) < 8192 * m + 4159 := by
  apply descent_of_endpoint
  · rw [data_13_4159.1]; exact data_13_4159.2.2
  · rw [data_13_4159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4199). -/
theorem data_13_4199 : oddCount 4199 13 = 8 ∧
    acceleratedOrbit 13 4199 = 3364 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4199 : ∀ j : Fin 13,
    4199 ≤ acceleratedOrbit j.val 4199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4199 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4199) = 6561 * m + 3364 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4199
  rw [data_13_4199.1, data_13_4199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4199 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4199) < 8192 * m + 4199 := by
  apply descent_of_endpoint
  · rw [data_13_4199.1]; exact data_13_4199.2.2
  · rw [data_13_4199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4223). -/
theorem data_13_4223 : oddCount 4223 13 = 8 ∧
    acceleratedOrbit 13 4223 = 3383 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4223 : ∀ j : Fin 13,
    4223 ≤ acceleratedOrbit j.val 4223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4223 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4223) = 6561 * m + 3383 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4223
  rw [data_13_4223.1, data_13_4223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4223 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4223) < 8192 * m + 4223 := by
  apply descent_of_endpoint
  · rw [data_13_4223.1]; exact data_13_4223.2.2
  · rw [data_13_4223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4251). -/
theorem data_13_4251 : oddCount 4251 13 = 8 ∧
    acceleratedOrbit 13 4251 = 3406 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4251 : ∀ j : Fin 13,
    4251 ≤ acceleratedOrbit j.val 4251 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4251 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4251) = 6561 * m + 3406 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4251
  rw [data_13_4251.1, data_13_4251.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4251 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4251) < 8192 * m + 4251 := by
  apply descent_of_endpoint
  · rw [data_13_4251.1]; exact data_13_4251.2.2
  · rw [data_13_4251.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4455). -/
theorem data_13_4455 : oddCount 4455 13 = 8 ∧
    acceleratedOrbit 13 4455 = 3569 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4455 : ∀ j : Fin 13,
    4455 ≤ acceleratedOrbit j.val 4455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4455 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4455) = 6561 * m + 3569 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4455
  rw [data_13_4455.1, data_13_4455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4455 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4455) < 8192 * m + 4455 := by
  apply descent_of_endpoint
  · rw [data_13_4455.1]; exact data_13_4455.2.2
  · rw [data_13_4455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4507). -/
theorem data_13_4507 : oddCount 4507 13 = 8 ∧
    acceleratedOrbit 13 4507 = 3611 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4507 : ∀ j : Fin 13,
    4507 ≤ acceleratedOrbit j.val 4507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4507 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4507) = 6561 * m + 3611 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4507
  rw [data_13_4507.1, data_13_4507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4507 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4507) < 8192 * m + 4507 := by
  apply descent_of_endpoint
  · rw [data_13_4507.1]; exact data_13_4507.2.2
  · rw [data_13_4507.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4859). -/
theorem data_13_4859 : oddCount 4859 13 = 8 ∧
    acceleratedOrbit 13 4859 = 3893 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4859 : ∀ j : Fin 13,
    4859 ≤ acceleratedOrbit j.val 4859 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4859 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4859) = 6561 * m + 3893 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4859
  rw [data_13_4859.1, data_13_4859.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4859 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4859) < 8192 * m + 4859 := by
  apply descent_of_endpoint
  · rw [data_13_4859.1]; exact data_13_4859.2.2
  · rw [data_13_4859.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 4927). -/
theorem data_13_4927 : oddCount 4927 13 = 8 ∧
    acceleratedOrbit 13 4927 = 3947 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_4927 : ∀ j : Fin 13,
    4927 ≤ acceleratedOrbit j.val 4927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_4927 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4927) = 6561 * m + 3947 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 4927
  rw [data_13_4927.1, data_13_4927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_4927 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 4927) < 8192 * m + 4927 := by
  apply descent_of_endpoint
  · rw [data_13_4927.1]; exact data_13_4927.2.2
  · rw [data_13_4927.2.1]; decide

end Collatz.Research.FirstDescent.Batch013
