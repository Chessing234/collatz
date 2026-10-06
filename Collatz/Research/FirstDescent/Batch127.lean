import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 127. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch127
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 58623). -/
theorem data_18_58623 : oddCount 58623 18 = 11 ∧
    acceleratedOrbit 18 58623 = 39616 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_58623 : ∀ j : Fin 18,
    58623 ≤ acceleratedOrbit j.val 58623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_58623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58623) = 177147 * m + 39616 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 58623
  rw [data_18_58623.1, data_18_58623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_58623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 58623) < 262144 * m + 58623 := by
  apply descent_of_endpoint
  · rw [data_18_58623.1]; exact data_18_58623.2.2
  · rw [data_18_58623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 59135). -/
theorem data_18_59135 : oddCount 59135 18 = 11 ∧
    acceleratedOrbit 18 59135 = 39962 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_59135 : ∀ j : Fin 18,
    59135 ≤ acceleratedOrbit j.val 59135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_59135 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59135) = 177147 * m + 39962 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 59135
  rw [data_18_59135.1, data_18_59135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_59135 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59135) < 262144 * m + 59135 := by
  apply descent_of_endpoint
  · rw [data_18_59135.1]; exact data_18_59135.2.2
  · rw [data_18_59135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 59227). -/
theorem data_18_59227 : oddCount 59227 18 = 11 ∧
    acceleratedOrbit 18 59227 = 40025 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_59227 : ∀ j : Fin 18,
    59227 ≤ acceleratedOrbit j.val 59227 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_59227 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59227) = 177147 * m + 40025 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 59227
  rw [data_18_59227.1, data_18_59227.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_59227 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59227) < 262144 * m + 59227 := by
  apply descent_of_endpoint
  · rw [data_18_59227.1]; exact data_18_59227.2.2
  · rw [data_18_59227.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 59387). -/
theorem data_18_59387 : oddCount 59387 18 = 11 ∧
    acceleratedOrbit 18 59387 = 40133 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_59387 : ∀ j : Fin 18,
    59387 ≤ acceleratedOrbit j.val 59387 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_59387 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59387) = 177147 * m + 40133 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 59387
  rw [data_18_59387.1, data_18_59387.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_59387 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59387) < 262144 * m + 59387 := by
  apply descent_of_endpoint
  · rw [data_18_59387.1]; exact data_18_59387.2.2
  · rw [data_18_59387.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 59599). -/
theorem data_18_59599 : oddCount 59599 18 = 11 ∧
    acceleratedOrbit 18 59599 = 40276 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_59599 : ∀ j : Fin 18,
    59599 ≤ acceleratedOrbit j.val 59599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_59599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59599) = 177147 * m + 40276 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 59599
  rw [data_18_59599.1, data_18_59599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_59599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59599) < 262144 * m + 59599 := by
  apply descent_of_endpoint
  · rw [data_18_59599.1]; exact data_18_59599.2.2
  · rw [data_18_59599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 59719). -/
theorem data_18_59719 : oddCount 59719 18 = 11 ∧
    acceleratedOrbit 18 59719 = 40357 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_59719 : ∀ j : Fin 18,
    59719 ≤ acceleratedOrbit j.val 59719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_59719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59719) = 177147 * m + 40357 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 59719
  rw [data_18_59719.1, data_18_59719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_59719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 59719) < 262144 * m + 59719 := by
  apply descent_of_endpoint
  · rw [data_18_59719.1]; exact data_18_59719.2.2
  · rw [data_18_59719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 60071). -/
theorem data_18_60071 : oddCount 60071 18 = 11 ∧
    acceleratedOrbit 18 60071 = 40595 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_60071 : ∀ j : Fin 18,
    60071 ≤ acceleratedOrbit j.val 60071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_60071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60071) = 177147 * m + 40595 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 60071
  rw [data_18_60071.1, data_18_60071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_60071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60071) < 262144 * m + 60071 := by
  apply descent_of_endpoint
  · rw [data_18_60071.1]; exact data_18_60071.2.2
  · rw [data_18_60071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 60111). -/
theorem data_18_60111 : oddCount 60111 18 = 11 ∧
    acceleratedOrbit 18 60111 = 40622 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_60111 : ∀ j : Fin 18,
    60111 ≤ acceleratedOrbit j.val 60111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_60111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60111) = 177147 * m + 40622 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 60111
  rw [data_18_60111.1, data_18_60111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_60111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60111) < 262144 * m + 60111 := by
  apply descent_of_endpoint
  · rw [data_18_60111.1]; exact data_18_60111.2.2
  · rw [data_18_60111.2.1]; decide

end Collatz.Research.FirstDescent.Batch127
