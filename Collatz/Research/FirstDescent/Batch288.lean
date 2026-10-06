import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 288. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch288
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 201375). -/
theorem data_20_201375 : oddCount 201375 20 = 12 ∧
    acceleratedOrbit 20 201375 = 102062 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_201375 : ∀ j : Fin 20,
    201375 ≤ acceleratedOrbit j.val 201375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_201375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201375) = 531441 * m + 102062 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 201375
  rw [data_20_201375.1, data_20_201375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_201375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201375) < 1048576 * m + 201375 := by
  apply descent_of_endpoint
  · rw [data_20_201375.1]; exact data_20_201375.2.2
  · rw [data_20_201375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 201499). -/
theorem data_20_201499 : oddCount 201499 20 = 12 ∧
    acceleratedOrbit 20 201499 = 102125 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_201499 : ∀ j : Fin 20,
    201499 ≤ acceleratedOrbit j.val 201499 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_201499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201499) = 531441 * m + 102125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 201499
  rw [data_20_201499.1, data_20_201499.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_201499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201499) < 1048576 * m + 201499 := by
  apply descent_of_endpoint
  · rw [data_20_201499.1]; exact data_20_201499.2.2
  · rw [data_20_201499.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 201775). -/
theorem data_20_201775 : oddCount 201775 20 = 12 ∧
    acceleratedOrbit 20 201775 = 102265 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_201775 : ∀ j : Fin 20,
    201775 ≤ acceleratedOrbit j.val 201775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_201775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201775) = 531441 * m + 102265 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 201775
  rw [data_20_201775.1, data_20_201775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_201775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201775) < 1048576 * m + 201775 := by
  apply descent_of_endpoint
  · rw [data_20_201775.1]; exact data_20_201775.2.2
  · rw [data_20_201775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 202663). -/
theorem data_20_202663 : oddCount 202663 20 = 12 ∧
    acceleratedOrbit 20 202663 = 102715 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_202663 : ∀ j : Fin 20,
    202663 ≤ acceleratedOrbit j.val 202663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_202663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 202663) = 531441 * m + 102715 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 202663
  rw [data_20_202663.1, data_20_202663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_202663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 202663) < 1048576 * m + 202663 := by
  apply descent_of_endpoint
  · rw [data_20_202663.1]; exact data_20_202663.2.2
  · rw [data_20_202663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 202687). -/
theorem data_20_202687 : oddCount 202687 20 = 12 ∧
    acceleratedOrbit 20 202687 = 102727 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_202687 : ∀ j : Fin 20,
    202687 ≤ acceleratedOrbit j.val 202687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_202687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 202687) = 531441 * m + 102727 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 202687
  rw [data_20_202687.1, data_20_202687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_202687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 202687) < 1048576 * m + 202687 := by
  apply descent_of_endpoint
  · rw [data_20_202687.1]; exact data_20_202687.2.2
  · rw [data_20_202687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 202991). -/
theorem data_20_202991 : oddCount 202991 20 = 12 ∧
    acceleratedOrbit 20 202991 = 102881 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_202991 : ∀ j : Fin 20,
    202991 ≤ acceleratedOrbit j.val 202991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_202991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 202991) = 531441 * m + 102881 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 202991
  rw [data_20_202991.1, data_20_202991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_202991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 202991) < 1048576 * m + 202991 := by
  apply descent_of_endpoint
  · rw [data_20_202991.1]; exact data_20_202991.2.2
  · rw [data_20_202991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 203007). -/
theorem data_20_203007 : oddCount 203007 20 = 12 ∧
    acceleratedOrbit 20 203007 = 102889 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_203007 : ∀ j : Fin 20,
    203007 ≤ acceleratedOrbit j.val 203007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_203007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 203007) = 531441 * m + 102889 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 203007
  rw [data_20_203007.1, data_20_203007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_203007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 203007) < 1048576 * m + 203007 := by
  apply descent_of_endpoint
  · rw [data_20_203007.1]; exact data_20_203007.2.2
  · rw [data_20_203007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 205287). -/
theorem data_20_205287 : oddCount 205287 20 = 12 ∧
    acceleratedOrbit 20 205287 = 104045 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_205287 : ∀ j : Fin 20,
    205287 ≤ acceleratedOrbit j.val 205287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_205287 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 205287) = 531441 * m + 104045 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 205287
  rw [data_20_205287.1, data_20_205287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_205287 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 205287) < 1048576 * m + 205287 := by
  apply descent_of_endpoint
  · rw [data_20_205287.1]; exact data_20_205287.2.2
  · rw [data_20_205287.2.1]; decide

end Collatz.Research.FirstDescent.Batch288
