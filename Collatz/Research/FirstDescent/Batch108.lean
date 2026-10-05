import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 108. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch108
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 17567). -/
theorem data_18_17567 : oddCount 17567 18 = 11 ∧
    acceleratedOrbit 18 17567 = 11872 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_17567 : ∀ j : Fin 18,
    17567 ≤ acceleratedOrbit j.val 17567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_17567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 17567) = 177147 * m + 11872 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 17567
  rw [data_18_17567.1, data_18_17567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_17567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 17567) < 262144 * m + 17567 := by
  apply descent_of_endpoint
  · rw [data_18_17567.1]; exact data_18_17567.2.2
  · rw [data_18_17567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 17639). -/
theorem data_18_17639 : oddCount 17639 18 = 11 ∧
    acceleratedOrbit 18 17639 = 11921 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_17639 : ∀ j : Fin 18,
    17639 ≤ acceleratedOrbit j.val 17639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_17639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 17639) = 177147 * m + 11921 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 17639
  rw [data_18_17639.1, data_18_17639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_17639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 17639) < 262144 * m + 17639 := by
  apply descent_of_endpoint
  · rw [data_18_17639.1]; exact data_18_17639.2.2
  · rw [data_18_17639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 18079). -/
theorem data_18_18079 : oddCount 18079 18 = 11 ∧
    acceleratedOrbit 18 18079 = 12218 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_18079 : ∀ j : Fin 18,
    18079 ≤ acceleratedOrbit j.val 18079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_18079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 18079) = 177147 * m + 12218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 18079
  rw [data_18_18079.1, data_18_18079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_18079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 18079) < 262144 * m + 18079 := by
  apply descent_of_endpoint
  · rw [data_18_18079.1]; exact data_18_18079.2.2
  · rw [data_18_18079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 18287). -/
theorem data_18_18287 : oddCount 18287 18 = 11 ∧
    acceleratedOrbit 18 18287 = 12359 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_18287 : ∀ j : Fin 18,
    18287 ≤ acceleratedOrbit j.val 18287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_18287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 18287) = 177147 * m + 12359 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 18287
  rw [data_18_18287.1, data_18_18287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_18287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 18287) < 262144 * m + 18287 := by
  apply descent_of_endpoint
  · rw [data_18_18287.1]; exact data_18_18287.2.2
  · rw [data_18_18287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 18687). -/
theorem data_18_18687 : oddCount 18687 18 = 11 ∧
    acceleratedOrbit 18 18687 = 12629 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_18687 : ∀ j : Fin 18,
    18687 ≤ acceleratedOrbit j.val 18687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_18687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 18687) = 177147 * m + 12629 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 18687
  rw [data_18_18687.1, data_18_18687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_18687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 18687) < 262144 * m + 18687 := by
  apply descent_of_endpoint
  · rw [data_18_18687.1]; exact data_18_18687.2.2
  · rw [data_18_18687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 19271). -/
theorem data_18_19271 : oddCount 19271 18 = 11 ∧
    acceleratedOrbit 18 19271 = 13024 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_19271 : ∀ j : Fin 18,
    19271 ≤ acceleratedOrbit j.val 19271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_19271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19271) = 177147 * m + 13024 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 19271
  rw [data_18_19271.1, data_18_19271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_19271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19271) < 262144 * m + 19271 := by
  apply descent_of_endpoint
  · rw [data_18_19271.1]; exact data_18_19271.2.2
  · rw [data_18_19271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 19311). -/
theorem data_18_19311 : oddCount 19311 18 = 11 ∧
    acceleratedOrbit 18 19311 = 13051 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_19311 : ∀ j : Fin 18,
    19311 ≤ acceleratedOrbit j.val 19311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_19311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19311) = 177147 * m + 13051 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 19311
  rw [data_18_19311.1, data_18_19311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_19311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19311) < 262144 * m + 19311 := by
  apply descent_of_endpoint
  · rw [data_18_19311.1]; exact data_18_19311.2.2
  · rw [data_18_19311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 19663). -/
theorem data_18_19663 : oddCount 19663 18 = 11 ∧
    acceleratedOrbit 18 19663 = 13289 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_19663 : ∀ j : Fin 18,
    19663 ≤ acceleratedOrbit j.val 19663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_19663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19663) = 177147 * m + 13289 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 19663
  rw [data_18_19663.1, data_18_19663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_19663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 19663) < 262144 * m + 19663 := by
  apply descent_of_endpoint
  · rw [data_18_19663.1]; exact data_18_19663.2.2
  · rw [data_18_19663.2.1]; decide

end Collatz.Research.FirstDescent.Batch108
