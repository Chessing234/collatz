import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 220. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch220
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 763). -/
theorem data_20_763 : oddCount 763 20 = 12 ∧
    acceleratedOrbit 20 763 = 388 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_763 : ∀ j : Fin 20,
    763 ≤ acceleratedOrbit j.val 763 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_763 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 763) = 531441 * m + 388 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 763
  rw [data_20_763.1, data_20_763.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_763 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 763) < 1048576 * m + 763 := by
  apply descent_of_endpoint
  · rw [data_20_763.1]; exact data_20_763.2.2
  · rw [data_20_763.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 1127). -/
theorem data_20_1127 : oddCount 1127 20 = 12 ∧
    acceleratedOrbit 20 1127 = 572 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_1127 : ∀ j : Fin 20,
    1127 ≤ acceleratedOrbit j.val 1127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_1127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1127) = 531441 * m + 572 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 1127
  rw [data_20_1127.1, data_20_1127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_1127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1127) < 1048576 * m + 1127 := by
  apply descent_of_endpoint
  · rw [data_20_1127.1]; exact data_20_1127.2.2
  · rw [data_20_1127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 1255). -/
theorem data_20_1255 : oddCount 1255 20 = 12 ∧
    acceleratedOrbit 20 1255 = 637 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_1255 : ∀ j : Fin 20,
    1255 ≤ acceleratedOrbit j.val 1255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_1255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1255) = 531441 * m + 637 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 1255
  rw [data_20_1255.1, data_20_1255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_1255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1255) < 1048576 * m + 1255 := by
  apply descent_of_endpoint
  · rw [data_20_1255.1]; exact data_20_1255.2.2
  · rw [data_20_1255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 1439). -/
theorem data_20_1439 : oddCount 1439 20 = 12 ∧
    acceleratedOrbit 20 1439 = 730 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_1439 : ∀ j : Fin 20,
    1439 ≤ acceleratedOrbit j.val 1439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_1439 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1439) = 531441 * m + 730 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 1439
  rw [data_20_1439.1, data_20_1439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_1439 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1439) < 1048576 * m + 1439 := by
  apply descent_of_endpoint
  · rw [data_20_1439.1]; exact data_20_1439.2.2
  · rw [data_20_1439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 1511). -/
theorem data_20_1511 : oddCount 1511 20 = 12 ∧
    acceleratedOrbit 20 1511 = 767 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_1511 : ∀ j : Fin 20,
    1511 ≤ acceleratedOrbit j.val 1511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_1511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1511) = 531441 * m + 767 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 1511
  rw [data_20_1511.1, data_20_1511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_1511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 1511) < 1048576 * m + 1511 := by
  apply descent_of_endpoint
  · rw [data_20_1511.1]; exact data_20_1511.2.2
  · rw [data_20_1511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 2139). -/
theorem data_20_2139 : oddCount 2139 20 = 12 ∧
    acceleratedOrbit 20 2139 = 1085 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_2139 : ∀ j : Fin 20,
    2139 ≤ acceleratedOrbit j.val 2139 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_2139 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2139) = 531441 * m + 1085 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 2139
  rw [data_20_2139.1, data_20_2139.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_2139 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2139) < 1048576 * m + 2139 := by
  apply descent_of_endpoint
  · rw [data_20_2139.1]; exact data_20_2139.2.2
  · rw [data_20_2139.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 2175). -/
theorem data_20_2175 : oddCount 2175 20 = 12 ∧
    acceleratedOrbit 20 2175 = 1103 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_2175 : ∀ j : Fin 20,
    2175 ≤ acceleratedOrbit j.val 2175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_2175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2175) = 531441 * m + 1103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 2175
  rw [data_20_2175.1, data_20_2175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_2175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2175) < 1048576 * m + 2175 := by
  apply descent_of_endpoint
  · rw [data_20_2175.1]; exact data_20_2175.2.2
  · rw [data_20_2175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 2255). -/
theorem data_20_2255 : oddCount 2255 20 = 12 ∧
    acceleratedOrbit 20 2255 = 1144 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_2255 : ∀ j : Fin 20,
    2255 ≤ acceleratedOrbit j.val 2255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_2255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2255) = 531441 * m + 1144 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 2255
  rw [data_20_2255.1, data_20_2255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_2255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2255) < 1048576 * m + 2255 := by
  apply descent_of_endpoint
  · rw [data_20_2255.1]; exact data_20_2255.2.2
  · rw [data_20_2255.2.1]; decide

end Collatz.Research.FirstDescent.Batch220
