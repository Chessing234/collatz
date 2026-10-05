import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 129. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch129
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 62063). -/
theorem data_18_62063 : oddCount 62063 18 = 11 ∧
    acceleratedOrbit 18 62063 = 41941 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_62063 : ∀ j : Fin 18,
    62063 ≤ acceleratedOrbit j.val 62063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_62063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62063) = 177147 * m + 41941 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 62063
  rw [data_18_62063.1, data_18_62063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_62063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62063) < 262144 * m + 62063 := by
  apply descent_of_endpoint
  · rw [data_18_62063.1]; exact data_18_62063.2.2
  · rw [data_18_62063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 62183). -/
theorem data_18_62183 : oddCount 62183 18 = 11 ∧
    acceleratedOrbit 18 62183 = 42022 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_62183 : ∀ j : Fin 18,
    62183 ≤ acceleratedOrbit j.val 62183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_62183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62183) = 177147 * m + 42022 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 62183
  rw [data_18_62183.1, data_18_62183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_62183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62183) < 262144 * m + 62183 := by
  apply descent_of_endpoint
  · rw [data_18_62183.1]; exact data_18_62183.2.2
  · rw [data_18_62183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 62575). -/
theorem data_18_62575 : oddCount 62575 18 = 11 ∧
    acceleratedOrbit 18 62575 = 42287 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_62575 : ∀ j : Fin 18,
    62575 ≤ acceleratedOrbit j.val 62575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_62575 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62575) = 177147 * m + 42287 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 62575
  rw [data_18_62575.1, data_18_62575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_62575 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62575) < 262144 * m + 62575 := by
  apply descent_of_endpoint
  · rw [data_18_62575.1]; exact data_18_62575.2.2
  · rw [data_18_62575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 62655). -/
theorem data_18_62655 : oddCount 62655 18 = 11 ∧
    acceleratedOrbit 18 62655 = 42341 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_62655 : ∀ j : Fin 18,
    62655 ≤ acceleratedOrbit j.val 62655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_62655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62655) = 177147 * m + 42341 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 62655
  rw [data_18_62655.1, data_18_62655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_62655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62655) < 262144 * m + 62655 := by
  apply descent_of_endpoint
  · rw [data_18_62655.1]; exact data_18_62655.2.2
  · rw [data_18_62655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 62695). -/
theorem data_18_62695 : oddCount 62695 18 = 11 ∧
    acceleratedOrbit 18 62695 = 42368 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_62695 : ∀ j : Fin 18,
    62695 ≤ acceleratedOrbit j.val 62695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_62695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62695) = 177147 * m + 42368 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 62695
  rw [data_18_62695.1, data_18_62695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_62695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62695) < 262144 * m + 62695 := by
  apply descent_of_endpoint
  · rw [data_18_62695.1]; exact data_18_62695.2.2
  · rw [data_18_62695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 62791). -/
theorem data_18_62791 : oddCount 62791 18 = 11 ∧
    acceleratedOrbit 18 62791 = 42433 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_62791 : ∀ j : Fin 18,
    62791 ≤ acceleratedOrbit j.val 62791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_62791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62791) = 177147 * m + 42433 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 62791
  rw [data_18_62791.1, data_18_62791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_62791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62791) < 262144 * m + 62791 := by
  apply descent_of_endpoint
  · rw [data_18_62791.1]; exact data_18_62791.2.2
  · rw [data_18_62791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 62975). -/
theorem data_18_62975 : oddCount 62975 18 = 11 ∧
    acceleratedOrbit 18 62975 = 42557 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_62975 : ∀ j : Fin 18,
    62975 ≤ acceleratedOrbit j.val 62975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_62975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62975) = 177147 * m + 42557 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 62975
  rw [data_18_62975.1, data_18_62975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_62975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 62975) < 262144 * m + 62975 := by
  apply descent_of_endpoint
  · rw [data_18_62975.1]; exact data_18_62975.2.2
  · rw [data_18_62975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 63183). -/
theorem data_18_63183 : oddCount 63183 18 = 11 ∧
    acceleratedOrbit 18 63183 = 42698 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_63183 : ∀ j : Fin 18,
    63183 ≤ acceleratedOrbit j.val 63183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_63183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63183) = 177147 * m + 42698 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 63183
  rw [data_18_63183.1, data_18_63183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_63183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63183) < 262144 * m + 63183 := by
  apply descent_of_endpoint
  · rw [data_18_63183.1]; exact data_18_63183.2.2
  · rw [data_18_63183.2.1]; decide

end Collatz.Research.FirstDescent.Batch129
