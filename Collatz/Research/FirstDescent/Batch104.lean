import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 104. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch104
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 9471). -/
theorem data_18_9471 : oddCount 9471 18 = 11 ∧
    acceleratedOrbit 18 9471 = 6401 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_9471 : ∀ j : Fin 18,
    9471 ≤ acceleratedOrbit j.val 9471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_9471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 9471) = 177147 * m + 6401 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 9471
  rw [data_18_9471.1, data_18_9471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_9471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 9471) < 262144 * m + 9471 := by
  apply descent_of_endpoint
  · rw [data_18_9471.1]; exact data_18_9471.2.2
  · rw [data_18_9471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 9883). -/
theorem data_18_9883 : oddCount 9883 18 = 11 ∧
    acceleratedOrbit 18 9883 = 6680 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_9883 : ∀ j : Fin 18,
    9883 ≤ acceleratedOrbit j.val 9883 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_9883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 9883) = 177147 * m + 6680 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 9883
  rw [data_18_9883.1, data_18_9883.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_9883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 9883) < 262144 * m + 9883 := by
  apply descent_of_endpoint
  · rw [data_18_9883.1]; exact data_18_9883.2.2
  · rw [data_18_9883.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 10095). -/
theorem data_18_10095 : oddCount 10095 18 = 11 ∧
    acceleratedOrbit 18 10095 = 6823 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_10095 : ∀ j : Fin 18,
    10095 ≤ acceleratedOrbit j.val 10095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_10095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10095) = 177147 * m + 6823 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 10095
  rw [data_18_10095.1, data_18_10095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_10095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10095) < 262144 * m + 10095 := by
  apply descent_of_endpoint
  · rw [data_18_10095.1]; exact data_18_10095.2.2
  · rw [data_18_10095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 10399). -/
theorem data_18_10399 : oddCount 10399 18 = 11 ∧
    acceleratedOrbit 18 10399 = 7028 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_10399 : ∀ j : Fin 18,
    10399 ≤ acceleratedOrbit j.val 10399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_10399 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10399) = 177147 * m + 7028 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 10399
  rw [data_18_10399.1, data_18_10399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_10399 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10399) < 262144 * m + 10399 := by
  apply descent_of_endpoint
  · rw [data_18_10399.1]; exact data_18_10399.2.2
  · rw [data_18_10399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 10447). -/
theorem data_18_10447 : oddCount 10447 18 = 11 ∧
    acceleratedOrbit 18 10447 = 7061 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_10447 : ∀ j : Fin 18,
    10447 ≤ acceleratedOrbit j.val 10447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_10447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10447) = 177147 * m + 7061 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 10447
  rw [data_18_10447.1, data_18_10447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_10447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10447) < 262144 * m + 10447 := by
  apply descent_of_endpoint
  · rw [data_18_10447.1]; exact data_18_10447.2.2
  · rw [data_18_10447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 10495). -/
theorem data_18_10495 : oddCount 10495 18 = 11 ∧
    acceleratedOrbit 18 10495 = 7093 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_10495 : ∀ j : Fin 18,
    10495 ≤ acceleratedOrbit j.val 10495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_10495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10495) = 177147 * m + 7093 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 10495
  rw [data_18_10495.1, data_18_10495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_10495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10495) < 262144 * m + 10495 := by
  apply descent_of_endpoint
  · rw [data_18_10495.1]; exact data_18_10495.2.2
  · rw [data_18_10495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 10567). -/
theorem data_18_10567 : oddCount 10567 18 = 11 ∧
    acceleratedOrbit 18 10567 = 7142 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_10567 : ∀ j : Fin 18,
    10567 ≤ acceleratedOrbit j.val 10567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_10567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10567) = 177147 * m + 7142 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 10567
  rw [data_18_10567.1, data_18_10567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_10567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 10567) < 262144 * m + 10567 := by
  apply descent_of_endpoint
  · rw [data_18_10567.1]; exact data_18_10567.2.2
  · rw [data_18_10567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 11007). -/
theorem data_18_11007 : oddCount 11007 18 = 11 ∧
    acceleratedOrbit 18 11007 = 7439 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_11007 : ∀ j : Fin 18,
    11007 ≤ acceleratedOrbit j.val 11007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_11007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11007) = 177147 * m + 7439 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 11007
  rw [data_18_11007.1, data_18_11007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_11007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 11007) < 262144 * m + 11007 := by
  apply descent_of_endpoint
  · rw [data_18_11007.1]; exact data_18_11007.2.2
  · rw [data_18_11007.2.1]; decide

end Collatz.Research.FirstDescent.Batch104
