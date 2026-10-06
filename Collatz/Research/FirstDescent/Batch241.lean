import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 241. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch241
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 57339). -/
theorem data_20_57339 : oddCount 57339 20 = 12 ∧
    acceleratedOrbit 20 57339 = 29062 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_57339 : ∀ j : Fin 20,
    57339 ≤ acceleratedOrbit j.val 57339 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_57339 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57339) = 531441 * m + 29062 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 57339
  rw [data_20_57339.1, data_20_57339.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_57339 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57339) < 1048576 * m + 57339 := by
  apply descent_of_endpoint
  · rw [data_20_57339.1]; exact data_20_57339.2.2
  · rw [data_20_57339.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 57499). -/
theorem data_20_57499 : oddCount 57499 20 = 12 ∧
    acceleratedOrbit 20 57499 = 29143 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_57499 : ∀ j : Fin 20,
    57499 ≤ acceleratedOrbit j.val 57499 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_57499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57499) = 531441 * m + 29143 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 57499
  rw [data_20_57499.1, data_20_57499.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_57499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57499) < 1048576 * m + 57499 := by
  apply descent_of_endpoint
  · rw [data_20_57499.1]; exact data_20_57499.2.2
  · rw [data_20_57499.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 57703). -/
theorem data_20_57703 : oddCount 57703 20 = 12 ∧
    acceleratedOrbit 20 57703 = 29246 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_57703 : ∀ j : Fin 20,
    57703 ≤ acceleratedOrbit j.val 57703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_57703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57703) = 531441 * m + 29246 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 57703
  rw [data_20_57703.1, data_20_57703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_57703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57703) < 1048576 * m + 57703 := by
  apply descent_of_endpoint
  · rw [data_20_57703.1]; exact data_20_57703.2.2
  · rw [data_20_57703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 57831). -/
theorem data_20_57831 : oddCount 57831 20 = 12 ∧
    acceleratedOrbit 20 57831 = 29311 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_57831 : ∀ j : Fin 20,
    57831 ≤ acceleratedOrbit j.val 57831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_57831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57831) = 531441 * m + 29311 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 57831
  rw [data_20_57831.1, data_20_57831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_57831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 57831) < 1048576 * m + 57831 := by
  apply descent_of_endpoint
  · rw [data_20_57831.1]; exact data_20_57831.2.2
  · rw [data_20_57831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 58139). -/
theorem data_20_58139 : oddCount 58139 20 = 12 ∧
    acceleratedOrbit 20 58139 = 29467 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_58139 : ∀ j : Fin 20,
    58139 ≤ acceleratedOrbit j.val 58139 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_58139 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58139) = 531441 * m + 29467 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 58139
  rw [data_20_58139.1, data_20_58139.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_58139 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58139) < 1048576 * m + 58139 := by
  apply descent_of_endpoint
  · rw [data_20_58139.1]; exact data_20_58139.2.2
  · rw [data_20_58139.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 58727). -/
theorem data_20_58727 : oddCount 58727 20 = 12 ∧
    acceleratedOrbit 20 58727 = 29765 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_58727 : ∀ j : Fin 20,
    58727 ≤ acceleratedOrbit j.val 58727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_58727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58727) = 531441 * m + 29765 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 58727
  rw [data_20_58727.1, data_20_58727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_58727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58727) < 1048576 * m + 58727 := by
  apply descent_of_endpoint
  · rw [data_20_58727.1]; exact data_20_58727.2.2
  · rw [data_20_58727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 58751). -/
theorem data_20_58751 : oddCount 58751 20 = 12 ∧
    acceleratedOrbit 20 58751 = 29777 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_58751 : ∀ j : Fin 20,
    58751 ≤ acceleratedOrbit j.val 58751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_58751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58751) = 531441 * m + 29777 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 58751
  rw [data_20_58751.1, data_20_58751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_58751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58751) < 1048576 * m + 58751 := by
  apply descent_of_endpoint
  · rw [data_20_58751.1]; exact data_20_58751.2.2
  · rw [data_20_58751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 58831). -/
theorem data_20_58831 : oddCount 58831 20 = 12 ∧
    acceleratedOrbit 20 58831 = 29818 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_58831 : ∀ j : Fin 20,
    58831 ≤ acceleratedOrbit j.val 58831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_58831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58831) = 531441 * m + 29818 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 58831
  rw [data_20_58831.1, data_20_58831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_58831 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 58831) < 1048576 * m + 58831 := by
  apply descent_of_endpoint
  · rw [data_20_58831.1]; exact data_20_58831.2.2
  · rw [data_20_58831.2.1]; decide

end Collatz.Research.FirstDescent.Batch241
