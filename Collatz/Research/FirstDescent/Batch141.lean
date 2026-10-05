import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 141. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch141
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 85531). -/
theorem data_18_85531 : oddCount 85531 18 = 11 ∧
    acceleratedOrbit 18 85531 = 57800 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_85531 : ∀ j : Fin 18,
    85531 ≤ acceleratedOrbit j.val 85531 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_85531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 85531) = 177147 * m + 57800 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 85531
  rw [data_18_85531.1, data_18_85531.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_85531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 85531) < 262144 * m + 85531 := by
  apply descent_of_endpoint
  · rw [data_18_85531.1]; exact data_18_85531.2.2
  · rw [data_18_85531.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 86495). -/
theorem data_18_86495 : oddCount 86495 18 = 11 ∧
    acceleratedOrbit 18 86495 = 58451 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_86495 : ∀ j : Fin 18,
    86495 ≤ acceleratedOrbit j.val 86495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_86495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86495) = 177147 * m + 58451 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 86495
  rw [data_18_86495.1, data_18_86495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_86495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86495) < 262144 * m + 86495 := by
  apply descent_of_endpoint
  · rw [data_18_86495.1]; exact data_18_86495.2.2
  · rw [data_18_86495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 86555). -/
theorem data_18_86555 : oddCount 86555 18 = 11 ∧
    acceleratedOrbit 18 86555 = 58492 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_86555 : ∀ j : Fin 18,
    86555 ≤ acceleratedOrbit j.val 86555 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_86555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86555) = 177147 * m + 58492 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 86555
  rw [data_18_86555.1, data_18_86555.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_86555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86555) < 262144 * m + 86555 := by
  apply descent_of_endpoint
  · rw [data_18_86555.1]; exact data_18_86555.2.2
  · rw [data_18_86555.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 86655). -/
theorem data_18_86655 : oddCount 86655 18 = 11 ∧
    acceleratedOrbit 18 86655 = 58559 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_86655 : ∀ j : Fin 18,
    86655 ≤ acceleratedOrbit j.val 86655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_86655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86655) = 177147 * m + 58559 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 86655
  rw [data_18_86655.1, data_18_86655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_86655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86655) < 262144 * m + 86655 := by
  apply descent_of_endpoint
  · rw [data_18_86655.1]; exact data_18_86655.2.2
  · rw [data_18_86655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 86911). -/
theorem data_18_86911 : oddCount 86911 18 = 11 ∧
    acceleratedOrbit 18 86911 = 58732 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_86911 : ∀ j : Fin 18,
    86911 ≤ acceleratedOrbit j.val 86911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_86911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86911) = 177147 * m + 58732 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 86911
  rw [data_18_86911.1, data_18_86911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_86911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 86911) < 262144 * m + 86911 := by
  apply descent_of_endpoint
  · rw [data_18_86911.1]; exact data_18_86911.2.2
  · rw [data_18_86911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 87143). -/
theorem data_18_87143 : oddCount 87143 18 = 11 ∧
    acceleratedOrbit 18 87143 = 58889 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_87143 : ∀ j : Fin 18,
    87143 ≤ acceleratedOrbit j.val 87143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_87143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 87143) = 177147 * m + 58889 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 87143
  rw [data_18_87143.1, data_18_87143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_87143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 87143) < 262144 * m + 87143 := by
  apply descent_of_endpoint
  · rw [data_18_87143.1]; exact data_18_87143.2.2
  · rw [data_18_87143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 88127). -/
theorem data_18_88127 : oddCount 88127 18 = 11 ∧
    acceleratedOrbit 18 88127 = 59554 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_88127 : ∀ j : Fin 18,
    88127 ≤ acceleratedOrbit j.val 88127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_88127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 88127) = 177147 * m + 59554 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 88127
  rw [data_18_88127.1, data_18_88127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_88127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 88127) < 262144 * m + 88127 := by
  apply descent_of_endpoint
  · rw [data_18_88127.1]; exact data_18_88127.2.2
  · rw [data_18_88127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 88167). -/
theorem data_18_88167 : oddCount 88167 18 = 11 ∧
    acceleratedOrbit 18 88167 = 59581 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_88167 : ∀ j : Fin 18,
    88167 ≤ acceleratedOrbit j.val 88167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_88167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 88167) = 177147 * m + 59581 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 88167
  rw [data_18_88167.1, data_18_88167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_88167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 88167) < 262144 * m + 88167 := by
  apply descent_of_endpoint
  · rw [data_18_88167.1]; exact data_18_88167.2.2
  · rw [data_18_88167.2.1]; decide

end Collatz.Research.FirstDescent.Batch141
