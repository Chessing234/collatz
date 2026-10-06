import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 215. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch215
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 253487). -/
theorem data_18_253487 : oddCount 253487 18 = 11 ∧
    acceleratedOrbit 18 253487 = 171298 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_253487 : ∀ j : Fin 18,
    253487 ≤ acceleratedOrbit j.val 253487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_253487 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253487) = 177147 * m + 171298 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 253487
  rw [data_18_253487.1, data_18_253487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_253487 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253487) < 262144 * m + 253487 := by
  apply descent_of_endpoint
  · rw [data_18_253487.1]; exact data_18_253487.2.2
  · rw [data_18_253487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 253759). -/
theorem data_18_253759 : oddCount 253759 18 = 11 ∧
    acceleratedOrbit 18 253759 = 171482 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_253759 : ∀ j : Fin 18,
    253759 ≤ acceleratedOrbit j.val 253759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_253759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253759) = 177147 * m + 171482 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 253759
  rw [data_18_253759.1, data_18_253759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_253759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253759) < 262144 * m + 253759 := by
  apply descent_of_endpoint
  · rw [data_18_253759.1]; exact data_18_253759.2.2
  · rw [data_18_253759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 253999). -/
theorem data_18_253999 : oddCount 253999 18 = 11 ∧
    acceleratedOrbit 18 253999 = 171644 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_253999 : ∀ j : Fin 18,
    253999 ≤ acceleratedOrbit j.val 253999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_253999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253999) = 177147 * m + 171644 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 253999
  rw [data_18_253999.1, data_18_253999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_253999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 253999) < 262144 * m + 253999 := by
  apply descent_of_endpoint
  · rw [data_18_253999.1]; exact data_18_253999.2.2
  · rw [data_18_253999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 254079). -/
theorem data_18_254079 : oddCount 254079 18 = 11 ∧
    acceleratedOrbit 18 254079 = 171698 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_254079 : ∀ j : Fin 18,
    254079 ≤ acceleratedOrbit j.val 254079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_254079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254079) = 177147 * m + 171698 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 254079
  rw [data_18_254079.1, data_18_254079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_254079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254079) < 262144 * m + 254079 := by
  apply descent_of_endpoint
  · rw [data_18_254079.1]; exact data_18_254079.2.2
  · rw [data_18_254079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 254175). -/
theorem data_18_254175 : oddCount 254175 18 = 11 ∧
    acceleratedOrbit 18 254175 = 171763 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_254175 : ∀ j : Fin 18,
    254175 ≤ acceleratedOrbit j.val 254175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_254175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254175) = 177147 * m + 171763 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 254175
  rw [data_18_254175.1, data_18_254175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_254175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254175) < 262144 * m + 254175 := by
  apply descent_of_endpoint
  · rw [data_18_254175.1]; exact data_18_254175.2.2
  · rw [data_18_254175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 254203). -/
theorem data_18_254203 : oddCount 254203 18 = 11 ∧
    acceleratedOrbit 18 254203 = 171782 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_254203 : ∀ j : Fin 18,
    254203 ≤ acceleratedOrbit j.val 254203 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_254203 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254203) = 177147 * m + 171782 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 254203
  rw [data_18_254203.1, data_18_254203.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_254203 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254203) < 262144 * m + 254203 := by
  apply descent_of_endpoint
  · rw [data_18_254203.1]; exact data_18_254203.2.2
  · rw [data_18_254203.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 254399). -/
theorem data_18_254399 : oddCount 254399 18 = 11 ∧
    acceleratedOrbit 18 254399 = 171914 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_254399 : ∀ j : Fin 18,
    254399 ≤ acceleratedOrbit j.val 254399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_254399 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254399) = 177147 * m + 171914 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 254399
  rw [data_18_254399.1, data_18_254399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_254399 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254399) < 262144 * m + 254399 := by
  apply descent_of_endpoint
  · rw [data_18_254399.1]; exact data_18_254399.2.2
  · rw [data_18_254399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 254619). -/
theorem data_18_254619 : oddCount 254619 18 = 11 ∧
    acceleratedOrbit 18 254619 = 172063 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_254619 : ∀ j : Fin 18,
    254619 ≤ acceleratedOrbit j.val 254619 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_254619 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254619) = 177147 * m + 172063 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 254619
  rw [data_18_254619.1, data_18_254619.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_254619 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 254619) < 262144 * m + 254619 := by
  apply descent_of_endpoint
  · rw [data_18_254619.1]; exact data_18_254619.2.2
  · rw [data_18_254619.2.1]; decide

end Collatz.Research.FirstDescent.Batch215
