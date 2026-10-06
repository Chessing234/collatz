import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 146. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch146
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98783). -/
theorem data_18_98783 : oddCount 98783 18 = 11 ∧
    acceleratedOrbit 18 98783 = 66755 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98783 : ∀ j : Fin 18,
    98783 ≤ acceleratedOrbit j.val 98783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98783) = 177147 * m + 66755 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98783
  rw [data_18_98783.1, data_18_98783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98783) < 262144 * m + 98783 := by
  apply descent_of_endpoint
  · rw [data_18_98783.1]; exact data_18_98783.2.2
  · rw [data_18_98783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98863). -/
theorem data_18_98863 : oddCount 98863 18 = 11 ∧
    acceleratedOrbit 18 98863 = 66809 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98863 : ∀ j : Fin 18,
    98863 ≤ acceleratedOrbit j.val 98863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98863) = 177147 * m + 66809 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98863
  rw [data_18_98863.1, data_18_98863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98863) < 262144 * m + 98863 := by
  apply descent_of_endpoint
  · rw [data_18_98863.1]; exact data_18_98863.2.2
  · rw [data_18_98863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 98907). -/
theorem data_18_98907 : oddCount 98907 18 = 11 ∧
    acceleratedOrbit 18 98907 = 66839 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_98907 : ∀ j : Fin 18,
    98907 ≤ acceleratedOrbit j.val 98907 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_98907 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98907) = 177147 * m + 66839 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 98907
  rw [data_18_98907.1, data_18_98907.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_98907 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 98907) < 262144 * m + 98907 := by
  apply descent_of_endpoint
  · rw [data_18_98907.1]; exact data_18_98907.2.2
  · rw [data_18_98907.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 100519). -/
theorem data_18_100519 : oddCount 100519 18 = 11 ∧
    acceleratedOrbit 18 100519 = 67928 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_100519 : ∀ j : Fin 18,
    100519 ≤ acceleratedOrbit j.val 100519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_100519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 100519) = 177147 * m + 67928 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 100519
  rw [data_18_100519.1, data_18_100519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_100519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 100519) < 262144 * m + 100519 := by
  apply descent_of_endpoint
  · rw [data_18_100519.1]; exact data_18_100519.2.2
  · rw [data_18_100519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 100799). -/
theorem data_18_100799 : oddCount 100799 18 = 11 ∧
    acceleratedOrbit 18 100799 = 68117 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_100799 : ∀ j : Fin 18,
    100799 ≤ acceleratedOrbit j.val 100799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_100799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 100799) = 177147 * m + 68117 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 100799
  rw [data_18_100799.1, data_18_100799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_100799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 100799) < 262144 * m + 100799 := by
  apply descent_of_endpoint
  · rw [data_18_100799.1]; exact data_18_100799.2.2
  · rw [data_18_100799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 101019). -/
theorem data_18_101019 : oddCount 101019 18 = 11 ∧
    acceleratedOrbit 18 101019 = 68266 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_101019 : ∀ j : Fin 18,
    101019 ≤ acceleratedOrbit j.val 101019 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_101019 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101019) = 177147 * m + 68266 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 101019
  rw [data_18_101019.1, data_18_101019.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_101019 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101019) < 262144 * m + 101019 := by
  apply descent_of_endpoint
  · rw [data_18_101019.1]; exact data_18_101019.2.2
  · rw [data_18_101019.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 101055). -/
theorem data_18_101055 : oddCount 101055 18 = 11 ∧
    acceleratedOrbit 18 101055 = 68290 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_101055 : ∀ j : Fin 18,
    101055 ≤ acceleratedOrbit j.val 101055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_101055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101055) = 177147 * m + 68290 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 101055
  rw [data_18_101055.1, data_18_101055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_101055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101055) < 262144 * m + 101055 := by
  apply descent_of_endpoint
  · rw [data_18_101055.1]; exact data_18_101055.2.2
  · rw [data_18_101055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 101407). -/
theorem data_18_101407 : oddCount 101407 18 = 11 ∧
    acceleratedOrbit 18 101407 = 68528 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_101407 : ∀ j : Fin 18,
    101407 ≤ acceleratedOrbit j.val 101407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_101407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101407) = 177147 * m + 68528 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 101407
  rw [data_18_101407.1, data_18_101407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_101407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101407) < 262144 * m + 101407 := by
  apply descent_of_endpoint
  · rw [data_18_101407.1]; exact data_18_101407.2.2
  · rw [data_18_101407.2.1]; decide

end Collatz.Research.FirstDescent.Batch146
