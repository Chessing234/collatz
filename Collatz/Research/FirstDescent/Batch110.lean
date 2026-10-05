import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 110. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch110
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 20763). -/
theorem data_18_20763 : oddCount 20763 18 = 11 ∧
    acceleratedOrbit 18 20763 = 14032 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_20763 : ∀ j : Fin 18,
    20763 ≤ acceleratedOrbit j.val 20763 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_20763 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20763) = 177147 * m + 14032 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 20763
  rw [data_18_20763.1, data_18_20763.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_20763 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20763) < 262144 * m + 20763 := by
  apply descent_of_endpoint
  · rw [data_18_20763.1]; exact data_18_20763.2.2
  · rw [data_18_20763.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 20799). -/
theorem data_18_20799 : oddCount 20799 18 = 11 ∧
    acceleratedOrbit 18 20799 = 14056 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_20799 : ∀ j : Fin 18,
    20799 ≤ acceleratedOrbit j.val 20799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_20799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20799) = 177147 * m + 14056 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 20799
  rw [data_18_20799.1, data_18_20799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_20799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 20799) < 262144 * m + 20799 := by
  apply descent_of_endpoint
  · rw [data_18_20799.1]; exact data_18_20799.2.2
  · rw [data_18_20799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 21151). -/
theorem data_18_21151 : oddCount 21151 18 = 11 ∧
    acceleratedOrbit 18 21151 = 14294 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_21151 : ∀ j : Fin 18,
    21151 ≤ acceleratedOrbit j.val 21151 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_21151 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 21151) = 177147 * m + 14294 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 21151
  rw [data_18_21151.1, data_18_21151.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_21151 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 21151) < 262144 * m + 21151 := by
  apply descent_of_endpoint
  · rw [data_18_21151.1]; exact data_18_21151.2.2
  · rw [data_18_21151.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 21275). -/
theorem data_18_21275 : oddCount 21275 18 = 11 ∧
    acceleratedOrbit 18 21275 = 14378 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_21275 : ∀ j : Fin 18,
    21275 ≤ acceleratedOrbit j.val 21275 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_21275 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 21275) = 177147 * m + 14378 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 21275
  rw [data_18_21275.1, data_18_21275.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_21275 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 21275) < 262144 * m + 21275 := by
  apply descent_of_endpoint
  · rw [data_18_21275.1]; exact data_18_21275.2.2
  · rw [data_18_21275.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 22767). -/
theorem data_18_22767 : oddCount 22767 18 = 11 ∧
    acceleratedOrbit 18 22767 = 15386 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_22767 : ∀ j : Fin 18,
    22767 ≤ acceleratedOrbit j.val 22767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_22767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 22767) = 177147 * m + 15386 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 22767
  rw [data_18_22767.1, data_18_22767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_22767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 22767) < 262144 * m + 22767 := by
  apply descent_of_endpoint
  · rw [data_18_22767.1]; exact data_18_22767.2.2
  · rw [data_18_22767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 22847). -/
theorem data_18_22847 : oddCount 22847 18 = 11 ∧
    acceleratedOrbit 18 22847 = 15440 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_22847 : ∀ j : Fin 18,
    22847 ≤ acceleratedOrbit j.val 22847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_22847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 22847) = 177147 * m + 15440 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 22847
  rw [data_18_22847.1, data_18_22847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_22847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 22847) < 262144 * m + 22847 := by
  apply descent_of_endpoint
  · rw [data_18_22847.1]; exact data_18_22847.2.2
  · rw [data_18_22847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 23023). -/
theorem data_18_23023 : oddCount 23023 18 = 11 ∧
    acceleratedOrbit 18 23023 = 15559 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_23023 : ∀ j : Fin 18,
    23023 ≤ acceleratedOrbit j.val 23023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_23023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 23023) = 177147 * m + 15559 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 23023
  rw [data_18_23023.1, data_18_23023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_23023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 23023) < 262144 * m + 23023 := by
  apply descent_of_endpoint
  · rw [data_18_23023.1]; exact data_18_23023.2.2
  · rw [data_18_23023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 23547). -/
theorem data_18_23547 : oddCount 23547 18 = 11 ∧
    acceleratedOrbit 18 23547 = 15914 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_23547 : ∀ j : Fin 18,
    23547 ≤ acceleratedOrbit j.val 23547 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_23547 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 23547) = 177147 * m + 15914 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 23547
  rw [data_18_23547.1, data_18_23547.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_23547 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 23547) < 262144 * m + 23547 := by
  apply descent_of_endpoint
  · rw [data_18_23547.1]; exact data_18_23547.2.2
  · rw [data_18_23547.2.1]; decide

end Collatz.Research.FirstDescent.Batch110
