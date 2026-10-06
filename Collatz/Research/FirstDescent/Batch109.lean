import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 109. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch109
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 19739). -/
theorem data_18_19739 : oddCount 19739 18 = 11 ∧
    acceleratedOrbit 18 19739 = 13340 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_19739 : ∀ j : Fin 18,
    19739 ≤ acceleratedOrbit j.val 19739 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_19739 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19739) = 177147 * m + 13340 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 19739
  rw [data_18_19739.1, data_18_19739.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_19739 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19739) < 262144 * m + 19739 := by
  apply descent_of_endpoint
  · rw [data_18_19739.1]; exact data_18_19739.2.2
  · rw [data_18_19739.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 19783). -/
theorem data_18_19783 : oddCount 19783 18 = 11 ∧
    acceleratedOrbit 18 19783 = 13370 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_19783 : ∀ j : Fin 18,
    19783 ≤ acceleratedOrbit j.val 19783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_19783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19783) = 177147 * m + 13370 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 19783
  rw [data_18_19783.1, data_18_19783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_19783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19783) < 262144 * m + 19783 := by
  apply descent_of_endpoint
  · rw [data_18_19783.1]; exact data_18_19783.2.2
  · rw [data_18_19783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 19871). -/
theorem data_18_19871 : oddCount 19871 18 = 11 ∧
    acceleratedOrbit 18 19871 = 13429 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_19871 : ∀ j : Fin 18,
    19871 ≤ acceleratedOrbit j.val 19871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_19871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19871) = 177147 * m + 13429 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 19871
  rw [data_18_19871.1, data_18_19871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_19871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19871) < 262144 * m + 19871 := by
  apply descent_of_endpoint
  · rw [data_18_19871.1]; exact data_18_19871.2.2
  · rw [data_18_19871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 20383). -/
theorem data_18_20383 : oddCount 20383 18 = 11 ∧
    acceleratedOrbit 18 20383 = 13775 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_20383 : ∀ j : Fin 18,
    20383 ≤ acceleratedOrbit j.val 20383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_20383 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20383) = 177147 * m + 13775 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 20383
  rw [data_18_20383.1, data_18_20383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_20383 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20383) < 262144 * m + 20383 := by
  apply descent_of_endpoint
  · rw [data_18_20383.1]; exact data_18_20383.2.2
  · rw [data_18_20383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 20391). -/
theorem data_18_20391 : oddCount 20391 18 = 11 ∧
    acceleratedOrbit 18 20391 = 13781 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_20391 : ∀ j : Fin 18,
    20391 ≤ acceleratedOrbit j.val 20391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_20391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20391) = 177147 * m + 13781 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 20391
  rw [data_18_20391.1, data_18_20391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_20391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20391) < 262144 * m + 20391 := by
  apply descent_of_endpoint
  · rw [data_18_20391.1]; exact data_18_20391.2.2
  · rw [data_18_20391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 20551). -/
theorem data_18_20551 : oddCount 20551 18 = 11 ∧
    acceleratedOrbit 18 20551 = 13889 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_20551 : ∀ j : Fin 18,
    20551 ≤ acceleratedOrbit j.val 20551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_20551 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20551) = 177147 * m + 13889 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 20551
  rw [data_18_20551.1, data_18_20551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_20551 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20551) < 262144 * m + 20551 := by
  apply descent_of_endpoint
  · rw [data_18_20551.1]; exact data_18_20551.2.2
  · rw [data_18_20551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 20671). -/
theorem data_18_20671 : oddCount 20671 18 = 11 ∧
    acceleratedOrbit 18 20671 = 13970 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_20671 : ∀ j : Fin 18,
    20671 ≤ acceleratedOrbit j.val 20671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_20671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20671) = 177147 * m + 13970 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 20671
  rw [data_18_20671.1, data_18_20671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_20671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20671) < 262144 * m + 20671 := by
  apply descent_of_endpoint
  · rw [data_18_20671.1]; exact data_18_20671.2.2
  · rw [data_18_20671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 20719). -/
theorem data_18_20719 : oddCount 20719 18 = 11 ∧
    acceleratedOrbit 18 20719 = 14002 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_20719 : ∀ j : Fin 18,
    20719 ≤ acceleratedOrbit j.val 20719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_20719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20719) = 177147 * m + 14002 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 20719
  rw [data_18_20719.1, data_18_20719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_20719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20719) < 262144 * m + 20719 := by
  apply descent_of_endpoint
  · rw [data_18_20719.1]; exact data_18_20719.2.2
  · rw [data_18_20719.2.1]; decide

end Collatz.Research.FirstDescent.Batch109
