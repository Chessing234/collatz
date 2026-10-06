import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 31. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch031
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 18751). -/
theorem data_15_18751 : oddCount 18751 15 = 9 ∧
    acceleratedOrbit 15 18751 = 11264 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_18751 : ∀ j : Fin 15,
    18751 ≤ acceleratedOrbit j.val 18751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_18751 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18751) = 19683 * m + 11264 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 18751
  rw [data_15_18751.1, data_15_18751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_18751 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18751) < 32768 * m + 18751 := by
  apply descent_of_endpoint
  · rw [data_15_18751.1]; exact data_15_18751.2.2
  · rw [data_15_18751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 18895). -/
theorem data_15_18895 : oddCount 18895 15 = 9 ∧
    acceleratedOrbit 15 18895 = 11351 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_18895 : ∀ j : Fin 15,
    18895 ≤ acceleratedOrbit j.val 18895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_18895 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18895) = 19683 * m + 11351 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 18895
  rw [data_15_18895.1, data_15_18895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_18895 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 18895) < 32768 * m + 18895 := by
  apply descent_of_endpoint
  · rw [data_15_18895.1]; exact data_15_18895.2.2
  · rw [data_15_18895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 19035). -/
theorem data_15_19035 : oddCount 19035 15 = 9 ∧
    acceleratedOrbit 15 19035 = 11435 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_19035 : ∀ j : Fin 15,
    19035 ≤ acceleratedOrbit j.val 19035 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_19035 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19035) = 19683 * m + 11435 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 19035
  rw [data_15_19035.1, data_15_19035.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_19035 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19035) < 32768 * m + 19035 := by
  apply descent_of_endpoint
  · rw [data_15_19035.1]; exact data_15_19035.2.2
  · rw [data_15_19035.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 19199). -/
theorem data_15_19199 : oddCount 19199 15 = 9 ∧
    acceleratedOrbit 15 19199 = 11533 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_19199 : ∀ j : Fin 15,
    19199 ≤ acceleratedOrbit j.val 19199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_19199 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19199) = 19683 * m + 11533 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 19199
  rw [data_15_19199.1, data_15_19199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_19199 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19199) < 32768 * m + 19199 := by
  apply descent_of_endpoint
  · rw [data_15_19199.1]; exact data_15_19199.2.2
  · rw [data_15_19199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 19623). -/
theorem data_15_19623 : oddCount 19623 15 = 9 ∧
    acceleratedOrbit 15 19623 = 11788 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_19623 : ∀ j : Fin 15,
    19623 ≤ acceleratedOrbit j.val 19623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_19623 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19623) = 19683 * m + 11788 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 19623
  rw [data_15_19623.1, data_15_19623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_19623 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19623) < 32768 * m + 19623 := by
  apply descent_of_endpoint
  · rw [data_15_19623.1]; exact data_15_19623.2.2
  · rw [data_15_19623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 19919). -/
theorem data_15_19919 : oddCount 19919 15 = 9 ∧
    acceleratedOrbit 15 19919 = 11966 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_19919 : ∀ j : Fin 15,
    19919 ≤ acceleratedOrbit j.val 19919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_19919 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19919) = 19683 * m + 11966 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 19919
  rw [data_15_19919.1, data_15_19919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_19919 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 19919) < 32768 * m + 19919 := by
  apply descent_of_endpoint
  · rw [data_15_19919.1]; exact data_15_19919.2.2
  · rw [data_15_19919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 20079). -/
theorem data_15_20079 : oddCount 20079 15 = 9 ∧
    acceleratedOrbit 15 20079 = 12062 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_20079 : ∀ j : Fin 15,
    20079 ≤ acceleratedOrbit j.val 20079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_20079 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20079) = 19683 * m + 12062 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 20079
  rw [data_15_20079.1, data_15_20079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_20079 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20079) < 32768 * m + 20079 := by
  apply descent_of_endpoint
  · rw [data_15_20079.1]; exact data_15_20079.2.2
  · rw [data_15_20079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 20199). -/
theorem data_15_20199 : oddCount 20199 15 = 9 ∧
    acceleratedOrbit 15 20199 = 12134 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_20199 : ∀ j : Fin 15,
    20199 ≤ acceleratedOrbit j.val 20199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_20199 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20199) = 19683 * m + 12134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 20199
  rw [data_15_20199.1, data_15_20199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_20199 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 20199) < 32768 * m + 20199 := by
  apply descent_of_endpoint
  · rw [data_15_20199.1]; exact data_15_20199.2.2
  · rw [data_15_20199.2.1]; decide

end Collatz.Research.FirstDescent.Batch031
