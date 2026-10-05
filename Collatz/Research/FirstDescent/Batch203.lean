import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 203. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch203
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 223487). -/
theorem data_18_223487 : oddCount 223487 18 = 11 ∧
    acceleratedOrbit 18 223487 = 151025 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_223487 : ∀ j : Fin 18,
    223487 ≤ acceleratedOrbit j.val 223487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_223487 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 223487) = 177147 * m + 151025 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 223487
  rw [data_18_223487.1, data_18_223487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_223487 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 223487) < 262144 * m + 223487 := by
  apply descent_of_endpoint
  · rw [data_18_223487.1]; exact data_18_223487.2.2
  · rw [data_18_223487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 223855). -/
theorem data_18_223855 : oddCount 223855 18 = 11 ∧
    acceleratedOrbit 18 223855 = 151274 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_223855 : ∀ j : Fin 18,
    223855 ≤ acceleratedOrbit j.val 223855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_223855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 223855) = 177147 * m + 151274 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 223855
  rw [data_18_223855.1, data_18_223855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_223855 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 223855) < 262144 * m + 223855 := by
  apply descent_of_endpoint
  · rw [data_18_223855.1]; exact data_18_223855.2.2
  · rw [data_18_223855.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 224027). -/
theorem data_18_224027 : oddCount 224027 18 = 11 ∧
    acceleratedOrbit 18 224027 = 151390 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_224027 : ∀ j : Fin 18,
    224027 ≤ acceleratedOrbit j.val 224027 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_224027 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224027) = 177147 * m + 151390 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 224027
  rw [data_18_224027.1, data_18_224027.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_224027 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224027) < 262144 * m + 224027 := by
  apply descent_of_endpoint
  · rw [data_18_224027.1]; exact data_18_224027.2.2
  · rw [data_18_224027.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 224539). -/
theorem data_18_224539 : oddCount 224539 18 = 11 ∧
    acceleratedOrbit 18 224539 = 151736 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_224539 : ∀ j : Fin 18,
    224539 ≤ acceleratedOrbit j.val 224539 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_224539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224539) = 177147 * m + 151736 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 224539
  rw [data_18_224539.1, data_18_224539.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_224539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224539) < 262144 * m + 224539 := by
  apply descent_of_endpoint
  · rw [data_18_224539.1]; exact data_18_224539.2.2
  · rw [data_18_224539.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 224719). -/
theorem data_18_224719 : oddCount 224719 18 = 11 ∧
    acceleratedOrbit 18 224719 = 151858 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_224719 : ∀ j : Fin 18,
    224719 ≤ acceleratedOrbit j.val 224719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_224719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224719) = 177147 * m + 151858 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 224719
  rw [data_18_224719.1, data_18_224719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_224719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224719) < 262144 * m + 224719 := by
  apply descent_of_endpoint
  · rw [data_18_224719.1]; exact data_18_224719.2.2
  · rw [data_18_224719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 224879). -/
theorem data_18_224879 : oddCount 224879 18 = 11 ∧
    acceleratedOrbit 18 224879 = 151966 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_224879 : ∀ j : Fin 18,
    224879 ≤ acceleratedOrbit j.val 224879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_224879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224879) = 177147 * m + 151966 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 224879
  rw [data_18_224879.1, data_18_224879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_224879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224879) < 262144 * m + 224879 := by
  apply descent_of_endpoint
  · rw [data_18_224879.1]; exact data_18_224879.2.2
  · rw [data_18_224879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 224999). -/
theorem data_18_224999 : oddCount 224999 18 = 11 ∧
    acceleratedOrbit 18 224999 = 152047 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_224999 : ∀ j : Fin 18,
    224999 ≤ acceleratedOrbit j.val 224999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_224999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224999) = 177147 * m + 152047 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 224999
  rw [data_18_224999.1, data_18_224999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_224999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 224999) < 262144 * m + 224999 := by
  apply descent_of_endpoint
  · rw [data_18_224999.1]; exact data_18_224999.2.2
  · rw [data_18_224999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 225191). -/
theorem data_18_225191 : oddCount 225191 18 = 11 ∧
    acceleratedOrbit 18 225191 = 152177 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_225191 : ∀ j : Fin 18,
    225191 ≤ acceleratedOrbit j.val 225191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_225191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225191) = 177147 * m + 152177 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 225191
  rw [data_18_225191.1, data_18_225191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_225191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 225191) < 262144 * m + 225191 := by
  apply descent_of_endpoint
  · rw [data_18_225191.1]; exact data_18_225191.2.2
  · rw [data_18_225191.2.1]; decide

end Collatz.Research.FirstDescent.Batch203
