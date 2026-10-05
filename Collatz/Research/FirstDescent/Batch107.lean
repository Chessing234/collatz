import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 107. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch107
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13727). -/
theorem data_18_13727 : oddCount 13727 18 = 11 ∧
    acceleratedOrbit 18 13727 = 9277 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13727 : ∀ j : Fin 18,
    13727 ≤ acceleratedOrbit j.val 13727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13727) = 177147 * m + 9277 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13727
  rw [data_18_13727.1, data_18_13727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13727) < 262144 * m + 13727 := by
  apply descent_of_endpoint
  · rw [data_18_13727.1]; exact data_18_13727.2.2
  · rw [data_18_13727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 14331). -/
theorem data_18_14331 : oddCount 14331 18 = 11 ∧
    acceleratedOrbit 18 14331 = 9686 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_14331 : ∀ j : Fin 18,
    14331 ≤ acceleratedOrbit j.val 14331 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_14331 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 14331) = 177147 * m + 9686 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 14331
  rw [data_18_14331.1, data_18_14331.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_14331 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 14331) < 262144 * m + 14331 := by
  apply descent_of_endpoint
  · rw [data_18_14331.1]; exact data_18_14331.2.2
  · rw [data_18_14331.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 15355). -/
theorem data_18_15355 : oddCount 15355 18 = 11 ∧
    acceleratedOrbit 18 15355 = 10378 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_15355 : ∀ j : Fin 18,
    15355 ≤ acceleratedOrbit j.val 15355 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_15355 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 15355) = 177147 * m + 10378 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 15355
  rw [data_18_15355.1, data_18_15355.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_15355 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 15355) < 262144 * m + 15355 := by
  apply descent_of_endpoint
  · rw [data_18_15355.1]; exact data_18_15355.2.2
  · rw [data_18_15355.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 15775). -/
theorem data_18_15775 : oddCount 15775 18 = 11 ∧
    acceleratedOrbit 18 15775 = 10661 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_15775 : ∀ j : Fin 18,
    15775 ≤ acceleratedOrbit j.val 15775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_15775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 15775) = 177147 * m + 10661 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 15775
  rw [data_18_15775.1, data_18_15775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_15775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 15775) < 262144 * m + 15775 := by
  apply descent_of_endpoint
  · rw [data_18_15775.1]; exact data_18_15775.2.2
  · rw [data_18_15775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 16031). -/
theorem data_18_16031 : oddCount 16031 18 = 11 ∧
    acceleratedOrbit 18 16031 = 10834 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_16031 : ∀ j : Fin 18,
    16031 ≤ acceleratedOrbit j.val 16031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_16031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16031) = 177147 * m + 10834 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 16031
  rw [data_18_16031.1, data_18_16031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_16031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16031) < 262144 * m + 16031 := by
  apply descent_of_endpoint
  · rw [data_18_16031.1]; exact data_18_16031.2.2
  · rw [data_18_16031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 16543). -/
theorem data_18_16543 : oddCount 16543 18 = 11 ∧
    acceleratedOrbit 18 16543 = 11180 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_16543 : ∀ j : Fin 18,
    16543 ≤ acceleratedOrbit j.val 16543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_16543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16543) = 177147 * m + 11180 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 16543
  rw [data_18_16543.1, data_18_16543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_16543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16543) < 262144 * m + 16543 := by
  apply descent_of_endpoint
  · rw [data_18_16543.1]; exact data_18_16543.2.2
  · rw [data_18_16543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 16667). -/
theorem data_18_16667 : oddCount 16667 18 = 11 ∧
    acceleratedOrbit 18 16667 = 11264 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_16667 : ∀ j : Fin 18,
    16667 ≤ acceleratedOrbit j.val 16667 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_16667 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16667) = 177147 * m + 11264 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 16667
  rw [data_18_16667.1, data_18_16667.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_16667 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16667) < 262144 * m + 16667 := by
  apply descent_of_endpoint
  · rw [data_18_16667.1]; exact data_18_16667.2.2
  · rw [data_18_16667.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 16795). -/
theorem data_18_16795 : oddCount 16795 18 = 11 ∧
    acceleratedOrbit 18 16795 = 11351 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_16795 : ∀ j : Fin 18,
    16795 ≤ acceleratedOrbit j.val 16795 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_16795 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16795) = 177147 * m + 11351 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 16795
  rw [data_18_16795.1, data_18_16795.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_16795 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 16795) < 262144 * m + 16795 := by
  apply descent_of_endpoint
  · rw [data_18_16795.1]; exact data_18_16795.2.2
  · rw [data_18_16795.2.1]; decide

end Collatz.Research.FirstDescent.Batch107
