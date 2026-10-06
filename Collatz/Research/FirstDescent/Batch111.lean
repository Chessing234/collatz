import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 111. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch111
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 23579). -/
theorem data_18_23579 : oddCount 23579 18 = 11 ∧
    acceleratedOrbit 18 23579 = 15935 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_23579 : ∀ j : Fin 18,
    23579 ≤ acceleratedOrbit j.val 23579 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_23579 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 23579) = 177147 * m + 15935 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 23579
  rw [data_18_23579.1, data_18_23579.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_23579 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 23579) < 262144 * m + 23579 := by
  apply descent_of_endpoint
  · rw [data_18_23579.1]; exact data_18_23579.2.2
  · rw [data_18_23579.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 24423). -/
theorem data_18_24423 : oddCount 24423 18 = 11 ∧
    acceleratedOrbit 18 24423 = 16505 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_24423 : ∀ j : Fin 18,
    24423 ≤ acceleratedOrbit j.val 24423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_24423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 24423) = 177147 * m + 16505 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 24423
  rw [data_18_24423.1, data_18_24423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_24423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 24423) < 262144 * m + 24423 := by
  apply descent_of_endpoint
  · rw [data_18_24423.1]; exact data_18_24423.2.2
  · rw [data_18_24423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 24479). -/
theorem data_18_24479 : oddCount 24479 18 = 11 ∧
    acceleratedOrbit 18 24479 = 16543 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_24479 : ∀ j : Fin 18,
    24479 ≤ acceleratedOrbit j.val 24479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_24479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 24479) = 177147 * m + 16543 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 24479
  rw [data_18_24479.1, data_18_24479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_24479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 24479) < 262144 * m + 24479 := by
  apply descent_of_endpoint
  · rw [data_18_24479.1]; exact data_18_24479.2.2
  · rw [data_18_24479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 24991). -/
theorem data_18_24991 : oddCount 24991 18 = 11 ∧
    acceleratedOrbit 18 24991 = 16889 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_24991 : ∀ j : Fin 18,
    24991 ≤ acceleratedOrbit j.val 24991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_24991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 24991) = 177147 * m + 16889 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 24991
  rw [data_18_24991.1, data_18_24991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_24991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 24991) < 262144 * m + 24991 := by
  apply descent_of_endpoint
  · rw [data_18_24991.1]; exact data_18_24991.2.2
  · rw [data_18_24991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 25071). -/
theorem data_18_25071 : oddCount 25071 18 = 11 ∧
    acceleratedOrbit 18 25071 = 16943 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_25071 : ∀ j : Fin 18,
    25071 ≤ acceleratedOrbit j.val 25071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_25071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 25071) = 177147 * m + 16943 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 25071
  rw [data_18_25071.1, data_18_25071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_25071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 25071) < 262144 * m + 25071 := by
  apply descent_of_endpoint
  · rw [data_18_25071.1]; exact data_18_25071.2.2
  · rw [data_18_25071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 25447). -/
theorem data_18_25447 : oddCount 25447 18 = 11 ∧
    acceleratedOrbit 18 25447 = 17197 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_25447 : ∀ j : Fin 18,
    25447 ≤ acceleratedOrbit j.val 25447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_25447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 25447) = 177147 * m + 17197 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 25447
  rw [data_18_25447.1, data_18_25447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_25447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 25447) < 262144 * m + 25447 := by
  apply descent_of_endpoint
  · rw [data_18_25447.1]; exact data_18_25447.2.2
  · rw [data_18_25447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 25759). -/
theorem data_18_25759 : oddCount 25759 18 = 11 ∧
    acceleratedOrbit 18 25759 = 17408 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_25759 : ∀ j : Fin 18,
    25759 ≤ acceleratedOrbit j.val 25759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_25759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 25759) = 177147 * m + 17408 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 25759
  rw [data_18_25759.1, data_18_25759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_25759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 25759) < 262144 * m + 25759 := by
  apply descent_of_endpoint
  · rw [data_18_25759.1]; exact data_18_25759.2.2
  · rw [data_18_25759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 26695). -/
theorem data_18_26695 : oddCount 26695 18 = 11 ∧
    acceleratedOrbit 18 26695 = 18041 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_26695 : ∀ j : Fin 18,
    26695 ≤ acceleratedOrbit j.val 26695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_26695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 26695) = 177147 * m + 18041 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 26695
  rw [data_18_26695.1, data_18_26695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_26695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 26695) < 262144 * m + 26695 := by
  apply descent_of_endpoint
  · rw [data_18_26695.1]; exact data_18_26695.2.2
  · rw [data_18_26695.2.1]; decide

end Collatz.Research.FirstDescent.Batch111
