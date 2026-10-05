import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 249. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch249
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 80551). -/
theorem data_20_80551 : oddCount 80551 20 = 12 ∧
    acceleratedOrbit 20 80551 = 40826 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_80551 : ∀ j : Fin 20,
    80551 ≤ acceleratedOrbit j.val 80551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_80551 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80551) = 531441 * m + 40826 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 80551
  rw [data_20_80551.1, data_20_80551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_80551 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80551) < 1048576 * m + 80551 := by
  apply descent_of_endpoint
  · rw [data_20_80551.1]; exact data_20_80551.2.2
  · rw [data_20_80551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 80575). -/
theorem data_20_80575 : oddCount 80575 20 = 12 ∧
    acceleratedOrbit 20 80575 = 40838 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_80575 : ∀ j : Fin 20,
    80575 ≤ acceleratedOrbit j.val 80575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_80575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80575) = 531441 * m + 40838 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 80575
  rw [data_20_80575.1, data_20_80575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_80575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80575) < 1048576 * m + 80575 := by
  apply descent_of_endpoint
  · rw [data_20_80575.1]; exact data_20_80575.2.2
  · rw [data_20_80575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 81343). -/
theorem data_20_81343 : oddCount 81343 20 = 12 ∧
    acceleratedOrbit 20 81343 = 41227 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_81343 : ∀ j : Fin 20,
    81343 ≤ acceleratedOrbit j.val 81343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_81343 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 81343) = 531441 * m + 41227 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 81343
  rw [data_20_81343.1, data_20_81343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_81343 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 81343) < 1048576 * m + 81343 := by
  apply descent_of_endpoint
  · rw [data_20_81343.1]; exact data_20_81343.2.2
  · rw [data_20_81343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 82023). -/
theorem data_20_82023 : oddCount 82023 20 = 12 ∧
    acceleratedOrbit 20 82023 = 41572 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_82023 : ∀ j : Fin 20,
    82023 ≤ acceleratedOrbit j.val 82023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_82023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82023) = 531441 * m + 41572 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 82023
  rw [data_20_82023.1, data_20_82023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_82023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82023) < 1048576 * m + 82023 := by
  apply descent_of_endpoint
  · rw [data_20_82023.1]; exact data_20_82023.2.2
  · rw [data_20_82023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 82479). -/
theorem data_20_82479 : oddCount 82479 20 = 12 ∧
    acceleratedOrbit 20 82479 = 41803 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_82479 : ∀ j : Fin 20,
    82479 ≤ acceleratedOrbit j.val 82479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_82479 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82479) = 531441 * m + 41803 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 82479
  rw [data_20_82479.1, data_20_82479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_82479 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82479) < 1048576 * m + 82479 := by
  apply descent_of_endpoint
  · rw [data_20_82479.1]; exact data_20_82479.2.2
  · rw [data_20_82479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 82751). -/
theorem data_20_82751 : oddCount 82751 20 = 12 ∧
    acceleratedOrbit 20 82751 = 41941 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_82751 : ∀ j : Fin 20,
    82751 ≤ acceleratedOrbit j.val 82751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_82751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82751) = 531441 * m + 41941 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 82751
  rw [data_20_82751.1, data_20_82751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_82751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82751) < 1048576 * m + 82751 := by
  apply descent_of_endpoint
  · rw [data_20_82751.1]; exact data_20_82751.2.2
  · rw [data_20_82751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 82911). -/
theorem data_20_82911 : oddCount 82911 20 = 12 ∧
    acceleratedOrbit 20 82911 = 42022 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_82911 : ∀ j : Fin 20,
    82911 ≤ acceleratedOrbit j.val 82911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_82911 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82911) = 531441 * m + 42022 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 82911
  rw [data_20_82911.1, data_20_82911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_82911 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 82911) < 1048576 * m + 82911 := by
  apply descent_of_endpoint
  · rw [data_20_82911.1]; exact data_20_82911.2.2
  · rw [data_20_82911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 83035). -/
theorem data_20_83035 : oddCount 83035 20 = 12 ∧
    acceleratedOrbit 20 83035 = 42085 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_83035 : ∀ j : Fin 20,
    83035 ≤ acceleratedOrbit j.val 83035 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_83035 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83035) = 531441 * m + 42085 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 83035
  rw [data_20_83035.1, data_20_83035.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_83035 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83035) < 1048576 * m + 83035 := by
  apply descent_of_endpoint
  · rw [data_20_83035.1]; exact data_20_83035.2.2
  · rw [data_20_83035.2.1]; decide

end Collatz.Research.FirstDescent.Batch249
