import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 23. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch023
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 6759). -/
theorem data_15_6759 : oddCount 6759 15 = 9 ∧
    acceleratedOrbit 15 6759 = 4061 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_6759 : ∀ j : Fin 15,
    6759 ≤ acceleratedOrbit j.val 6759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_6759 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6759) = 19683 * m + 4061 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 6759
  rw [data_15_6759.1, data_15_6759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_6759 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6759) < 32768 * m + 6759 := by
  apply descent_of_endpoint
  · rw [data_15_6759.1]; exact data_15_6759.2.2
  · rw [data_15_6759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 6783). -/
theorem data_15_6783 : oddCount 6783 15 = 9 ∧
    acceleratedOrbit 15 6783 = 4075 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_6783 : ∀ j : Fin 15,
    6783 ≤ acceleratedOrbit j.val 6783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_6783 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6783) = 19683 * m + 4075 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 6783
  rw [data_15_6783.1, data_15_6783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_6783 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6783) < 32768 * m + 6783 := by
  apply descent_of_endpoint
  · rw [data_15_6783.1]; exact data_15_6783.2.2
  · rw [data_15_6783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 6907). -/
theorem data_15_6907 : oddCount 6907 15 = 9 ∧
    acceleratedOrbit 15 6907 = 4150 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_6907 : ∀ j : Fin 15,
    6907 ≤ acceleratedOrbit j.val 6907 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_6907 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6907) = 19683 * m + 4150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 6907
  rw [data_15_6907.1, data_15_6907.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_6907 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6907) < 32768 * m + 6907 := by
  apply descent_of_endpoint
  · rw [data_15_6907.1]; exact data_15_6907.2.2
  · rw [data_15_6907.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 7163). -/
theorem data_15_7163 : oddCount 7163 15 = 9 ∧
    acceleratedOrbit 15 7163 = 4304 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_7163 : ∀ j : Fin 15,
    7163 ≤ acceleratedOrbit j.val 7163 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_7163 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7163) = 19683 * m + 4304 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 7163
  rw [data_15_7163.1, data_15_7163.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_7163 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7163) < 32768 * m + 7163 := by
  apply descent_of_endpoint
  · rw [data_15_7163.1]; exact data_15_7163.2.2
  · rw [data_15_7163.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 7199). -/
theorem data_15_7199 : oddCount 7199 15 = 9 ∧
    acceleratedOrbit 15 7199 = 4325 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_7199 : ∀ j : Fin 15,
    7199 ≤ acceleratedOrbit j.val 7199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_7199 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7199) = 19683 * m + 4325 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 7199
  rw [data_15_7199.1, data_15_7199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_7199 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7199) < 32768 * m + 7199 := by
  apply descent_of_endpoint
  · rw [data_15_7199.1]; exact data_15_7199.2.2
  · rw [data_15_7199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 7487). -/
theorem data_15_7487 : oddCount 7487 15 = 9 ∧
    acceleratedOrbit 15 7487 = 4498 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_7487 : ∀ j : Fin 15,
    7487 ≤ acceleratedOrbit j.val 7487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_7487 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7487) = 19683 * m + 4498 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 7487
  rw [data_15_7487.1, data_15_7487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_7487 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7487) < 32768 * m + 7487 := by
  apply descent_of_endpoint
  · rw [data_15_7487.1]; exact data_15_7487.2.2
  · rw [data_15_7487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 7783). -/
theorem data_15_7783 : oddCount 7783 15 = 9 ∧
    acceleratedOrbit 15 7783 = 4676 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_7783 : ∀ j : Fin 15,
    7783 ≤ acceleratedOrbit j.val 7783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_7783 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7783) = 19683 * m + 4676 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 7783
  rw [data_15_7783.1, data_15_7783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_7783 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 7783) < 32768 * m + 7783 := by
  apply descent_of_endpoint
  · rw [data_15_7783.1]; exact data_15_7783.2.2
  · rw [data_15_7783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 8063). -/
theorem data_15_8063 : oddCount 8063 15 = 9 ∧
    acceleratedOrbit 15 8063 = 4844 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_8063 : ∀ j : Fin 15,
    8063 ≤ acceleratedOrbit j.val 8063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_8063 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8063) = 19683 * m + 4844 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 8063
  rw [data_15_8063.1, data_15_8063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_8063 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 8063) < 32768 * m + 8063 := by
  apply descent_of_endpoint
  · rw [data_15_8063.1]; exact data_15_8063.2.2
  · rw [data_15_8063.2.1]; decide

end Collatz.Research.FirstDescent.Batch023
