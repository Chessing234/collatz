import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 264. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch264
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 133031). -/
theorem data_20_133031 : oddCount 133031 20 = 12 ∧
    acceleratedOrbit 20 133031 = 67424 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_133031 : ∀ j : Fin 20,
    133031 ≤ acceleratedOrbit j.val 133031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_133031 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 133031) = 531441 * m + 67424 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 133031
  rw [data_20_133031.1, data_20_133031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_133031 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 133031) < 1048576 * m + 133031 := by
  apply descent_of_endpoint
  · rw [data_20_133031.1]; exact data_20_133031.2.2
  · rw [data_20_133031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 133723). -/
theorem data_20_133723 : oddCount 133723 20 = 12 ∧
    acceleratedOrbit 20 133723 = 67775 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_133723 : ∀ j : Fin 20,
    133723 ≤ acceleratedOrbit j.val 133723 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_133723 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 133723) = 531441 * m + 67775 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 133723
  rw [data_20_133723.1, data_20_133723.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_133723 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 133723) < 1048576 * m + 133723 := by
  apply descent_of_endpoint
  · rw [data_20_133723.1]; exact data_20_133723.2.2
  · rw [data_20_133723.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 133883). -/
theorem data_20_133883 : oddCount 133883 20 = 12 ∧
    acceleratedOrbit 20 133883 = 67856 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_133883 : ∀ j : Fin 20,
    133883 ≤ acceleratedOrbit j.val 133883 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_133883 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 133883) = 531441 * m + 67856 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 133883
  rw [data_20_133883.1, data_20_133883.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_133883 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 133883) < 1048576 * m + 133883 := by
  apply descent_of_endpoint
  · rw [data_20_133883.1]; exact data_20_133883.2.2
  · rw [data_20_133883.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 134399). -/
theorem data_20_134399 : oddCount 134399 20 = 12 ∧
    acceleratedOrbit 20 134399 = 68117 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_134399 : ∀ j : Fin 20,
    134399 ≤ acceleratedOrbit j.val 134399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_134399 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 134399) = 531441 * m + 68117 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 134399
  rw [data_20_134399.1, data_20_134399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_134399 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 134399) < 1048576 * m + 134399 := by
  apply descent_of_endpoint
  · rw [data_20_134399.1]; exact data_20_134399.2.2
  · rw [data_20_134399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 134811). -/
theorem data_20_134811 : oddCount 134811 20 = 12 ∧
    acceleratedOrbit 20 134811 = 68326 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_134811 : ∀ j : Fin 20,
    134811 ≤ acceleratedOrbit j.val 134811 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_134811 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 134811) = 531441 * m + 68326 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 134811
  rw [data_20_134811.1, data_20_134811.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_134811 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 134811) < 1048576 * m + 134811 := by
  apply descent_of_endpoint
  · rw [data_20_134811.1]; exact data_20_134811.2.2
  · rw [data_20_134811.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 135215). -/
theorem data_20_135215 : oddCount 135215 20 = 12 ∧
    acceleratedOrbit 20 135215 = 68531 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_135215 : ∀ j : Fin 20,
    135215 ≤ acceleratedOrbit j.val 135215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_135215 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 135215) = 531441 * m + 68531 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 135215
  rw [data_20_135215.1, data_20_135215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_135215 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 135215) < 1048576 * m + 135215 := by
  apply descent_of_endpoint
  · rw [data_20_135215.1]; exact data_20_135215.2.2
  · rw [data_20_135215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 135375). -/
theorem data_20_135375 : oddCount 135375 20 = 12 ∧
    acceleratedOrbit 20 135375 = 68612 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_135375 : ∀ j : Fin 20,
    135375 ≤ acceleratedOrbit j.val 135375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_135375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 135375) = 531441 * m + 68612 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 135375
  rw [data_20_135375.1, data_20_135375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_135375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 135375) < 1048576 * m + 135375 := by
  apply descent_of_endpoint
  · rw [data_20_135375.1]; exact data_20_135375.2.2
  · rw [data_20_135375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 136239). -/
theorem data_20_136239 : oddCount 136239 20 = 12 ∧
    acceleratedOrbit 20 136239 = 69050 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_136239 : ∀ j : Fin 20,
    136239 ≤ acceleratedOrbit j.val 136239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_136239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136239) = 531441 * m + 69050 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 136239
  rw [data_20_136239.1, data_20_136239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_136239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136239) < 1048576 * m + 136239 := by
  apply descent_of_endpoint
  · rw [data_20_136239.1]; exact data_20_136239.2.2
  · rw [data_20_136239.2.1]; decide

end Collatz.Research.FirstDescent.Batch264
