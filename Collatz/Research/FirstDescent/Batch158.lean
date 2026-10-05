import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 158. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch158
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 120319). -/
theorem data_18_120319 : oddCount 120319 18 = 11 ∧
    acceleratedOrbit 18 120319 = 81308 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_120319 : ∀ j : Fin 18,
    120319 ≤ acceleratedOrbit j.val 120319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_120319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 120319) = 177147 * m + 81308 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 120319
  rw [data_18_120319.1, data_18_120319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_120319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 120319) < 262144 * m + 120319 := by
  apply descent_of_endpoint
  · rw [data_18_120319.1]; exact data_18_120319.2.2
  · rw [data_18_120319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 122015). -/
theorem data_18_122015 : oddCount 122015 18 = 11 ∧
    acceleratedOrbit 18 122015 = 82454 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_122015 : ∀ j : Fin 18,
    122015 ≤ acceleratedOrbit j.val 122015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_122015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122015) = 177147 * m + 82454 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 122015
  rw [data_18_122015.1, data_18_122015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_122015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122015) < 262144 * m + 122015 := by
  apply descent_of_endpoint
  · rw [data_18_122015.1]; exact data_18_122015.2.2
  · rw [data_18_122015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 122095). -/
theorem data_18_122095 : oddCount 122095 18 = 11 ∧
    acceleratedOrbit 18 122095 = 82508 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_122095 : ∀ j : Fin 18,
    122095 ≤ acceleratedOrbit j.val 122095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_122095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122095) = 177147 * m + 82508 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 122095
  rw [data_18_122095.1, data_18_122095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_122095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122095) < 262144 * m + 122095 := by
  apply descent_of_endpoint
  · rw [data_18_122095.1]; exact data_18_122095.2.2
  · rw [data_18_122095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 122267). -/
theorem data_18_122267 : oddCount 122267 18 = 11 ∧
    acceleratedOrbit 18 122267 = 82625 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_122267 : ∀ j : Fin 18,
    122267 ≤ acceleratedOrbit j.val 122267 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_122267 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122267) = 177147 * m + 82625 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 122267
  rw [data_18_122267.1, data_18_122267.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_122267 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122267) < 262144 * m + 122267 := by
  apply descent_of_endpoint
  · rw [data_18_122267.1]; exact data_18_122267.2.2
  · rw [data_18_122267.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 122271). -/
theorem data_18_122271 : oddCount 122271 18 = 11 ∧
    acceleratedOrbit 18 122271 = 82627 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_122271 : ∀ j : Fin 18,
    122271 ≤ acceleratedOrbit j.val 122271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_122271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122271) = 177147 * m + 82627 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 122271
  rw [data_18_122271.1, data_18_122271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_122271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122271) < 262144 * m + 122271 := by
  apply descent_of_endpoint
  · rw [data_18_122271.1]; exact data_18_122271.2.2
  · rw [data_18_122271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 122875). -/
theorem data_18_122875 : oddCount 122875 18 = 11 ∧
    acceleratedOrbit 18 122875 = 83036 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_122875 : ∀ j : Fin 18,
    122875 ≤ acceleratedOrbit j.val 122875 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_122875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122875) = 177147 * m + 83036 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 122875
  rw [data_18_122875.1, data_18_122875.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_122875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122875) < 262144 * m + 122875 := by
  apply descent_of_endpoint
  · rw [data_18_122875.1]; exact data_18_122875.2.2
  · rw [data_18_122875.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 122907). -/
theorem data_18_122907 : oddCount 122907 18 = 11 ∧
    acceleratedOrbit 18 122907 = 83057 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_122907 : ∀ j : Fin 18,
    122907 ≤ acceleratedOrbit j.val 122907 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_122907 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122907) = 177147 * m + 83057 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 122907
  rw [data_18_122907.1, data_18_122907.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_122907 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 122907) < 262144 * m + 122907 := by
  apply descent_of_endpoint
  · rw [data_18_122907.1]; exact data_18_122907.2.2
  · rw [data_18_122907.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 123035). -/
theorem data_18_123035 : oddCount 123035 18 = 11 ∧
    acceleratedOrbit 18 123035 = 83144 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_123035 : ∀ j : Fin 18,
    123035 ≤ acceleratedOrbit j.val 123035 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_123035 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123035) = 177147 * m + 83144 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 123035
  rw [data_18_123035.1, data_18_123035.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_123035 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 123035) < 262144 * m + 123035 := by
  apply descent_of_endpoint
  · rw [data_18_123035.1]; exact data_18_123035.2.2
  · rw [data_18_123035.2.1]; decide

end Collatz.Research.FirstDescent.Batch158
