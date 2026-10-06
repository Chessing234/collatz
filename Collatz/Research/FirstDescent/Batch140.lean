import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 140. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch140
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84199). -/
theorem data_18_84199 : oddCount 84199 18 = 11 ∧
    acceleratedOrbit 18 84199 = 56900 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84199 : ∀ j : Fin 18,
    84199 ≤ acceleratedOrbit j.val 84199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84199) = 177147 * m + 56900 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84199
  rw [data_18_84199.1, data_18_84199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84199) < 262144 * m + 84199 := by
  apply descent_of_endpoint
  · rw [data_18_84199.1]; exact data_18_84199.2.2
  · rw [data_18_84199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84327). -/
theorem data_18_84327 : oddCount 84327 18 = 11 ∧
    acceleratedOrbit 18 84327 = 56986 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84327 : ∀ j : Fin 18,
    84327 ≤ acceleratedOrbit j.val 84327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84327) = 177147 * m + 56986 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84327
  rw [data_18_84327.1, data_18_84327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84327) < 262144 * m + 84327 := by
  apply descent_of_endpoint
  · rw [data_18_84327.1]; exact data_18_84327.2.2
  · rw [data_18_84327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84447). -/
theorem data_18_84447 : oddCount 84447 18 = 11 ∧
    acceleratedOrbit 18 84447 = 57067 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84447 : ∀ j : Fin 18,
    84447 ≤ acceleratedOrbit j.val 84447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84447) = 177147 * m + 57067 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84447
  rw [data_18_84447.1, data_18_84447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84447) < 262144 * m + 84447 := by
  apply descent_of_endpoint
  · rw [data_18_84447.1]; exact data_18_84447.2.2
  · rw [data_18_84447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84607). -/
theorem data_18_84607 : oddCount 84607 18 = 11 ∧
    acceleratedOrbit 18 84607 = 57175 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84607 : ∀ j : Fin 18,
    84607 ≤ acceleratedOrbit j.val 84607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84607) = 177147 * m + 57175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84607
  rw [data_18_84607.1, data_18_84607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84607) < 262144 * m + 84607 := by
  apply descent_of_endpoint
  · rw [data_18_84607.1]; exact data_18_84607.2.2
  · rw [data_18_84607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84639). -/
theorem data_18_84639 : oddCount 84639 18 = 11 ∧
    acceleratedOrbit 18 84639 = 57197 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84639 : ∀ j : Fin 18,
    84639 ≤ acceleratedOrbit j.val 84639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84639) = 177147 * m + 57197 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84639
  rw [data_18_84639.1, data_18_84639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84639) < 262144 * m + 84639 := by
  apply descent_of_endpoint
  · rw [data_18_84639.1]; exact data_18_84639.2.2
  · rw [data_18_84639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84719). -/
theorem data_18_84719 : oddCount 84719 18 = 11 ∧
    acceleratedOrbit 18 84719 = 57251 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84719 : ∀ j : Fin 18,
    84719 ≤ acceleratedOrbit j.val 84719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84719) = 177147 * m + 57251 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84719
  rw [data_18_84719.1, data_18_84719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84719) < 262144 * m + 84719 := by
  apply descent_of_endpoint
  · rw [data_18_84719.1]; exact data_18_84719.2.2
  · rw [data_18_84719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84799). -/
theorem data_18_84799 : oddCount 84799 18 = 11 ∧
    acceleratedOrbit 18 84799 = 57305 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84799 : ∀ j : Fin 18,
    84799 ≤ acceleratedOrbit j.val 84799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84799) = 177147 * m + 57305 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84799
  rw [data_18_84799.1, data_18_84799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84799) < 262144 * m + 84799 := by
  apply descent_of_endpoint
  · rw [data_18_84799.1]; exact data_18_84799.2.2
  · rw [data_18_84799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84839). -/
theorem data_18_84839 : oddCount 84839 18 = 11 ∧
    acceleratedOrbit 18 84839 = 57332 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84839 : ∀ j : Fin 18,
    84839 ≤ acceleratedOrbit j.val 84839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84839) = 177147 * m + 57332 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84839
  rw [data_18_84839.1, data_18_84839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84839 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84839) < 262144 * m + 84839 := by
  apply descent_of_endpoint
  · rw [data_18_84839.1]; exact data_18_84839.2.2
  · rw [data_18_84839.2.1]; decide

end Collatz.Research.FirstDescent.Batch140
