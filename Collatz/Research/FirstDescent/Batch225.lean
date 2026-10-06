import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 225. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch225
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 11111). -/
theorem data_20_11111 : oddCount 11111 20 = 12 ∧
    acceleratedOrbit 20 11111 = 5632 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_11111 : ∀ j : Fin 20,
    11111 ≤ acceleratedOrbit j.val 11111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_11111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11111) = 531441 * m + 5632 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 11111
  rw [data_20_11111.1, data_20_11111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_11111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11111) < 1048576 * m + 11111 := by
  apply descent_of_endpoint
  · rw [data_20_11111.1]; exact data_20_11111.2.2
  · rw [data_20_11111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 11355). -/
theorem data_20_11355 : oddCount 11355 20 = 12 ∧
    acceleratedOrbit 20 11355 = 5756 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_11355 : ∀ j : Fin 20,
    11355 ≤ acceleratedOrbit j.val 11355 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_11355 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11355) = 531441 * m + 5756 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 11355
  rw [data_20_11355.1, data_20_11355.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_11355 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11355) < 1048576 * m + 11355 := by
  apply descent_of_endpoint
  · rw [data_20_11355.1]; exact data_20_11355.2.2
  · rw [data_20_11355.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 11471). -/
theorem data_20_11471 : oddCount 11471 20 = 12 ∧
    acceleratedOrbit 20 11471 = 5815 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_11471 : ∀ j : Fin 20,
    11471 ≤ acceleratedOrbit j.val 11471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_11471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11471) = 531441 * m + 5815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 11471
  rw [data_20_11471.1, data_20_11471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_11471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11471) < 1048576 * m + 11471 := by
  apply descent_of_endpoint
  · rw [data_20_11471.1]; exact data_20_11471.2.2
  · rw [data_20_11471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 11711). -/
theorem data_20_11711 : oddCount 11711 20 = 12 ∧
    acceleratedOrbit 20 11711 = 5936 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_11711 : ∀ j : Fin 20,
    11711 ≤ acceleratedOrbit j.val 11711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_11711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11711) = 531441 * m + 5936 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 11711
  rw [data_20_11711.1, data_20_11711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_11711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11711) < 1048576 * m + 11711 := by
  apply descent_of_endpoint
  · rw [data_20_11711.1]; exact data_20_11711.2.2
  · rw [data_20_11711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 11803). -/
theorem data_20_11803 : oddCount 11803 20 = 12 ∧
    acceleratedOrbit 20 11803 = 5983 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_11803 : ∀ j : Fin 20,
    11803 ≤ acceleratedOrbit j.val 11803 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_11803 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11803) = 531441 * m + 5983 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 11803
  rw [data_20_11803.1, data_20_11803.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_11803 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 11803) < 1048576 * m + 11803 := by
  apply descent_of_endpoint
  · rw [data_20_11803.1]; exact data_20_11803.2.2
  · rw [data_20_11803.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 12379). -/
theorem data_20_12379 : oddCount 12379 20 = 12 ∧
    acceleratedOrbit 20 12379 = 6275 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_12379 : ∀ j : Fin 20,
    12379 ≤ acceleratedOrbit j.val 12379 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_12379 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 12379) = 531441 * m + 6275 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 12379
  rw [data_20_12379.1, data_20_12379.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_12379 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 12379) < 1048576 * m + 12379 := by
  apply descent_of_endpoint
  · rw [data_20_12379.1]; exact data_20_12379.2.2
  · rw [data_20_12379.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 12847). -/
theorem data_20_12847 : oddCount 12847 20 = 12 ∧
    acceleratedOrbit 20 12847 = 6512 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_12847 : ∀ j : Fin 20,
    12847 ≤ acceleratedOrbit j.val 12847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_12847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 12847) = 531441 * m + 6512 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 12847
  rw [data_20_12847.1, data_20_12847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_12847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 12847) < 1048576 * m + 12847 := by
  apply descent_of_endpoint
  · rw [data_20_12847.1]; exact data_20_12847.2.2
  · rw [data_20_12847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 13159). -/
theorem data_20_13159 : oddCount 13159 20 = 12 ∧
    acceleratedOrbit 20 13159 = 6670 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_13159 : ∀ j : Fin 20,
    13159 ≤ acceleratedOrbit j.val 13159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_13159 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 13159) = 531441 * m + 6670 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 13159
  rw [data_20_13159.1, data_20_13159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_13159 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 13159) < 1048576 * m + 13159 := by
  apply descent_of_endpoint
  · rw [data_20_13159.1]; exact data_20_13159.2.2
  · rw [data_20_13159.2.1]; decide

end Collatz.Research.FirstDescent.Batch225
