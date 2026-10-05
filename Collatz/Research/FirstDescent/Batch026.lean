import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 26. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch026
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 11079). -/
theorem data_15_11079 : oddCount 11079 15 = 9 ∧
    acceleratedOrbit 15 11079 = 6656 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_11079 : ∀ j : Fin 15,
    11079 ≤ acceleratedOrbit j.val 11079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_11079 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11079) = 19683 * m + 6656 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 11079
  rw [data_15_11079.1, data_15_11079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_11079 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11079) < 32768 * m + 11079 := by
  apply descent_of_endpoint
  · rw [data_15_11079.1]; exact data_15_11079.2.2
  · rw [data_15_11079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 11119). -/
theorem data_15_11119 : oddCount 11119 15 = 9 ∧
    acceleratedOrbit 15 11119 = 6680 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_11119 : ∀ j : Fin 15,
    11119 ≤ acceleratedOrbit j.val 11119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_11119 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11119) = 19683 * m + 6680 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 11119
  rw [data_15_11119.1, data_15_11119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_11119 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11119) < 32768 * m + 11119 := by
  apply descent_of_endpoint
  · rw [data_15_11119.1]; exact data_15_11119.2.2
  · rw [data_15_11119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 11567). -/
theorem data_15_11567 : oddCount 11567 15 = 9 ∧
    acceleratedOrbit 15 11567 = 6949 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_11567 : ∀ j : Fin 15,
    11567 ≤ acceleratedOrbit j.val 11567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_11567 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11567) = 19683 * m + 6949 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 11567
  rw [data_15_11567.1, data_15_11567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_11567 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11567) < 32768 * m + 11567 := by
  apply descent_of_endpoint
  · rw [data_15_11567.1]; exact data_15_11567.2.2
  · rw [data_15_11567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 11679). -/
theorem data_15_11679 : oddCount 11679 15 = 9 ∧
    acceleratedOrbit 15 11679 = 7016 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_11679 : ∀ j : Fin 15,
    11679 ≤ acceleratedOrbit j.val 11679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_11679 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11679) = 19683 * m + 7016 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 11679
  rw [data_15_11679.1, data_15_11679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_11679 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11679) < 32768 * m + 11679 := by
  apply descent_of_endpoint
  · rw [data_15_11679.1]; exact data_15_11679.2.2
  · rw [data_15_11679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 11807). -/
theorem data_15_11807 : oddCount 11807 15 = 9 ∧
    acceleratedOrbit 15 11807 = 7093 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_11807 : ∀ j : Fin 15,
    11807 ≤ acceleratedOrbit j.val 11807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_11807 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11807) = 19683 * m + 7093 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 11807
  rw [data_15_11807.1, data_15_11807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_11807 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11807) < 32768 * m + 11807 := by
  apply descent_of_endpoint
  · rw [data_15_11807.1]; exact data_15_11807.2.2
  · rw [data_15_11807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 11943). -/
theorem data_15_11943 : oddCount 11943 15 = 9 ∧
    acceleratedOrbit 15 11943 = 7175 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_11943 : ∀ j : Fin 15,
    11943 ≤ acceleratedOrbit j.val 11943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_11943 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11943) = 19683 * m + 7175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 11943
  rw [data_15_11943.1, data_15_11943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_11943 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11943) < 32768 * m + 11943 := by
  apply descent_of_endpoint
  · rw [data_15_11943.1]; exact data_15_11943.2.2
  · rw [data_15_11943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 11967). -/
theorem data_15_11967 : oddCount 11967 15 = 9 ∧
    acceleratedOrbit 15 11967 = 7189 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_11967 : ∀ j : Fin 15,
    11967 ≤ acceleratedOrbit j.val 11967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_11967 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11967) = 19683 * m + 7189 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 11967
  rw [data_15_11967.1, data_15_11967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_11967 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 11967) < 32768 * m + 11967 := by
  apply descent_of_endpoint
  · rw [data_15_11967.1]; exact data_15_11967.2.2
  · rw [data_15_11967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 12063). -/
theorem data_15_12063 : oddCount 12063 15 = 9 ∧
    acceleratedOrbit 15 12063 = 7247 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_12063 : ∀ j : Fin 15,
    12063 ≤ acceleratedOrbit j.val 12063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_12063 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12063) = 19683 * m + 7247 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 12063
  rw [data_15_12063.1, data_15_12063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_12063 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12063) < 32768 * m + 12063 := by
  apply descent_of_endpoint
  · rw [data_15_12063.1]; exact data_15_12063.2.2
  · rw [data_15_12063.2.1]; decide

end Collatz.Research.FirstDescent.Batch026
