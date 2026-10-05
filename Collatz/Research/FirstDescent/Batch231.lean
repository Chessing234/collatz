import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 231. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch231
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 28367). -/
theorem data_20_28367 : oddCount 28367 20 = 12 ∧
    acceleratedOrbit 20 28367 = 14378 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_28367 : ∀ j : Fin 20,
    28367 ≤ acceleratedOrbit j.val 28367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_28367 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 28367) = 531441 * m + 14378 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 28367
  rw [data_20_28367.1, data_20_28367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_28367 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 28367) < 1048576 * m + 28367 := by
  apply descent_of_endpoint
  · rw [data_20_28367.1]; exact data_20_28367.2.2
  · rw [data_20_28367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 29211). -/
theorem data_20_29211 : oddCount 29211 20 = 12 ∧
    acceleratedOrbit 20 29211 = 14806 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_29211 : ∀ j : Fin 20,
    29211 ≤ acceleratedOrbit j.val 29211 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_29211 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 29211) = 531441 * m + 14806 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 29211
  rw [data_20_29211.1, data_20_29211.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_29211 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 29211) < 1048576 * m + 29211 := by
  apply descent_of_endpoint
  · rw [data_20_29211.1]; exact data_20_29211.2.2
  · rw [data_20_29211.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 29415). -/
theorem data_20_29415 : oddCount 29415 20 = 12 ∧
    acceleratedOrbit 20 29415 = 14909 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_29415 : ∀ j : Fin 20,
    29415 ≤ acceleratedOrbit j.val 29415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_29415 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 29415) = 531441 * m + 14909 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 29415
  rw [data_20_29415.1, data_20_29415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_29415 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 29415) < 1048576 * m + 29415 := by
  apply descent_of_endpoint
  · rw [data_20_29415.1]; exact data_20_29415.2.2
  · rw [data_20_29415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 29727). -/
theorem data_20_29727 : oddCount 29727 20 = 12 ∧
    acceleratedOrbit 20 29727 = 15067 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_29727 : ∀ j : Fin 20,
    29727 ≤ acceleratedOrbit j.val 29727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_29727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 29727) = 531441 * m + 15067 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 29727
  rw [data_20_29727.1, data_20_29727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_29727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 29727) < 1048576 * m + 29727 := by
  apply descent_of_endpoint
  · rw [data_20_29727.1]; exact data_20_29727.2.2
  · rw [data_20_29727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 31131). -/
theorem data_20_31131 : oddCount 31131 20 = 12 ∧
    acceleratedOrbit 20 31131 = 15779 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_31131 : ∀ j : Fin 20,
    31131 ≤ acceleratedOrbit j.val 31131 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_31131 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31131) = 531441 * m + 15779 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 31131
  rw [data_20_31131.1, data_20_31131.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_31131 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31131) < 1048576 * m + 31131 := by
  apply descent_of_endpoint
  · rw [data_20_31131.1]; exact data_20_31131.2.2
  · rw [data_20_31131.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 31279). -/
theorem data_20_31279 : oddCount 31279 20 = 12 ∧
    acceleratedOrbit 20 31279 = 15854 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_31279 : ∀ j : Fin 20,
    31279 ≤ acceleratedOrbit j.val 31279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_31279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31279) = 531441 * m + 15854 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 31279
  rw [data_20_31279.1, data_20_31279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_31279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31279) < 1048576 * m + 31279 := by
  apply descent_of_endpoint
  · rw [data_20_31279.1]; exact data_20_31279.2.2
  · rw [data_20_31279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 31439). -/
theorem data_20_31439 : oddCount 31439 20 = 12 ∧
    acceleratedOrbit 20 31439 = 15935 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_31439 : ∀ j : Fin 20,
    31439 ≤ acceleratedOrbit j.val 31439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_31439 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31439) = 531441 * m + 15935 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 31439
  rw [data_20_31439.1, data_20_31439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_31439 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31439) < 1048576 * m + 31439 := by
  apply descent_of_endpoint
  · rw [data_20_31439.1]; exact data_20_31439.2.2
  · rw [data_20_31439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 31487). -/
theorem data_20_31487 : oddCount 31487 20 = 12 ∧
    acceleratedOrbit 20 31487 = 15959 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_31487 : ∀ j : Fin 20,
    31487 ≤ acceleratedOrbit j.val 31487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_31487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31487) = 531441 * m + 15959 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 31487
  rw [data_20_31487.1, data_20_31487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_31487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 31487) < 1048576 * m + 31487 := by
  apply descent_of_endpoint
  · rw [data_20_31487.1]; exact data_20_31487.2.2
  · rw [data_20_31487.2.1]; decide

end Collatz.Research.FirstDescent.Batch231
