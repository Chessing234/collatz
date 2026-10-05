import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 145. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch145
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 97895). -/
theorem data_18_97895 : oddCount 97895 18 = 11 ∧
    acceleratedOrbit 18 97895 = 66155 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_97895 : ∀ j : Fin 18,
    97895 ≤ acceleratedOrbit j.val 97895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_97895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 97895) = 177147 * m + 66155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 97895
  rw [data_18_97895.1, data_18_97895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_97895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 97895) < 262144 * m + 97895 := by
  apply descent_of_endpoint
  · rw [data_18_97895.1]; exact data_18_97895.2.2
  · rw [data_18_97895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98175). -/
theorem data_18_98175 : oddCount 98175 18 = 11 ∧
    acceleratedOrbit 18 98175 = 66344 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98175 : ∀ j : Fin 18,
    98175 ≤ acceleratedOrbit j.val 98175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98175) = 177147 * m + 66344 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98175
  rw [data_18_98175.1, data_18_98175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98175) < 262144 * m + 98175 := by
  apply descent_of_endpoint
  · rw [data_18_98175.1]; exact data_18_98175.2.2
  · rw [data_18_98175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98335). -/
theorem data_18_98335 : oddCount 98335 18 = 11 ∧
    acceleratedOrbit 18 98335 = 66452 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98335 : ∀ j : Fin 18,
    98335 ≤ acceleratedOrbit j.val 98335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98335) = 177147 * m + 66452 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98335
  rw [data_18_98335.1, data_18_98335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98335) < 262144 * m + 98335 := by
  apply descent_of_endpoint
  · rw [data_18_98335.1]; exact data_18_98335.2.2
  · rw [data_18_98335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98351). -/
theorem data_18_98351 : oddCount 98351 18 = 11 ∧
    acceleratedOrbit 18 98351 = 66463 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98351 : ∀ j : Fin 18,
    98351 ≤ acceleratedOrbit j.val 98351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98351) = 177147 * m + 66463 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98351
  rw [data_18_98351.1, data_18_98351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98351) < 262144 * m + 98351 := by
  apply descent_of_endpoint
  · rw [data_18_98351.1]; exact data_18_98351.2.2
  · rw [data_18_98351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98471). -/
theorem data_18_98471 : oddCount 98471 18 = 11 ∧
    acceleratedOrbit 18 98471 = 66544 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98471 : ∀ j : Fin 18,
    98471 ≤ acceleratedOrbit j.val 98471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98471) = 177147 * m + 66544 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98471
  rw [data_18_98471.1, data_18_98471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98471) < 262144 * m + 98471 := by
  apply descent_of_endpoint
  · rw [data_18_98471.1]; exact data_18_98471.2.2
  · rw [data_18_98471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98555). -/
theorem data_18_98555 : oddCount 98555 18 = 11 ∧
    acceleratedOrbit 18 98555 = 66601 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98555 : ∀ j : Fin 18,
    98555 ≤ acceleratedOrbit j.val 98555 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98555) = 177147 * m + 66601 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98555
  rw [data_18_98555.1, data_18_98555.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98555) < 262144 * m + 98555 := by
  apply descent_of_endpoint
  · rw [data_18_98555.1]; exact data_18_98555.2.2
  · rw [data_18_98555.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98663). -/
theorem data_18_98663 : oddCount 98663 18 = 11 ∧
    acceleratedOrbit 18 98663 = 66674 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98663 : ∀ j : Fin 18,
    98663 ≤ acceleratedOrbit j.val 98663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98663) = 177147 * m + 66674 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98663
  rw [data_18_98663.1, data_18_98663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98663) < 262144 * m + 98663 := by
  apply descent_of_endpoint
  · rw [data_18_98663.1]; exact data_18_98663.2.2
  · rw [data_18_98663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98751). -/
theorem data_18_98751 : oddCount 98751 18 = 11 ∧
    acceleratedOrbit 18 98751 = 66733 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98751 : ∀ j : Fin 18,
    98751 ≤ acceleratedOrbit j.val 98751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98751) = 177147 * m + 66733 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98751
  rw [data_18_98751.1, data_18_98751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98751) < 262144 * m + 98751 := by
  apply descent_of_endpoint
  · rw [data_18_98751.1]; exact data_18_98751.2.2
  · rw [data_18_98751.2.1]; decide

end Collatz.Research.FirstDescent.Batch145
