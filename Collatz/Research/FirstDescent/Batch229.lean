import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 229. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch229
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 21247). -/
theorem data_20_21247 : oddCount 21247 20 = 12 ∧
    acceleratedOrbit 20 21247 = 10769 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_21247 : ∀ j : Fin 20,
    21247 ≤ acceleratedOrbit j.val 21247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_21247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 21247) = 531441 * m + 10769 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 21247
  rw [data_20_21247.1, data_20_21247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_21247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 21247) < 1048576 * m + 21247 := by
  apply descent_of_endpoint
  · rw [data_20_21247.1]; exact data_20_21247.2.2
  · rw [data_20_21247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 21375). -/
theorem data_20_21375 : oddCount 21375 20 = 12 ∧
    acceleratedOrbit 20 21375 = 10834 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_21375 : ∀ j : Fin 20,
    21375 ≤ acceleratedOrbit j.val 21375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_21375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 21375) = 531441 * m + 10834 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 21375
  rw [data_20_21375.1, data_20_21375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_21375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 21375) < 1048576 * m + 21375 := by
  apply descent_of_endpoint
  · rw [data_20_21375.1]; exact data_20_21375.2.2
  · rw [data_20_21375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 22223). -/
theorem data_20_22223 : oddCount 22223 20 = 12 ∧
    acceleratedOrbit 20 22223 = 11264 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_22223 : ∀ j : Fin 20,
    22223 ≤ acceleratedOrbit j.val 22223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_22223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 22223) = 531441 * m + 11264 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 22223
  rw [data_20_22223.1, data_20_22223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_22223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 22223) < 1048576 * m + 22223 := by
  apply descent_of_endpoint
  · rw [data_20_22223.1]; exact data_20_22223.2.2
  · rw [data_20_22223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 23087). -/
theorem data_20_23087 : oddCount 23087 20 = 12 ∧
    acceleratedOrbit 20 23087 = 11702 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_23087 : ∀ j : Fin 20,
    23087 ≤ acceleratedOrbit j.val 23087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_23087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23087) = 531441 * m + 11702 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 23087
  rw [data_20_23087.1, data_20_23087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_23087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23087) < 1048576 * m + 23087 := by
  apply descent_of_endpoint
  · rw [data_20_23087.1]; exact data_20_23087.2.2
  · rw [data_20_23087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 23271). -/
theorem data_20_23271 : oddCount 23271 20 = 12 ∧
    acceleratedOrbit 20 23271 = 11795 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_23271 : ∀ j : Fin 20,
    23271 ≤ acceleratedOrbit j.val 23271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_23271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23271) = 531441 * m + 11795 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 23271
  rw [data_20_23271.1, data_20_23271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_23271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23271) < 1048576 * m + 23271 := by
  apply descent_of_endpoint
  · rw [data_20_23271.1]; exact data_20_23271.2.2
  · rw [data_20_23271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 23295). -/
theorem data_20_23295 : oddCount 23295 20 = 12 ∧
    acceleratedOrbit 20 23295 = 11807 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_23295 : ∀ j : Fin 20,
    23295 ≤ acceleratedOrbit j.val 23295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_23295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23295) = 531441 * m + 11807 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 23295
  rw [data_20_23295.1, data_20_23295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_23295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23295) < 1048576 * m + 23295 := by
  apply descent_of_endpoint
  · rw [data_20_23295.1]; exact data_20_23295.2.2
  · rw [data_20_23295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 23423). -/
theorem data_20_23423 : oddCount 23423 20 = 12 ∧
    acceleratedOrbit 20 23423 = 11872 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_23423 : ∀ j : Fin 20,
    23423 ≤ acceleratedOrbit j.val 23423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_23423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23423) = 531441 * m + 11872 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 23423
  rw [data_20_23423.1, data_20_23423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_23423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23423) < 1048576 * m + 23423 := by
  apply descent_of_endpoint
  · rw [data_20_23423.1]; exact data_20_23423.2.2
  · rw [data_20_23423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 23519). -/
theorem data_20_23519 : oddCount 23519 20 = 12 ∧
    acceleratedOrbit 20 23519 = 11921 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_23519 : ∀ j : Fin 20,
    23519 ≤ acceleratedOrbit j.val 23519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_23519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23519) = 531441 * m + 11921 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 23519
  rw [data_20_23519.1, data_20_23519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_23519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 23519) < 1048576 * m + 23519 := by
  apply descent_of_endpoint
  · rw [data_20_23519.1]; exact data_20_23519.2.2
  · rw [data_20_23519.2.1]; decide

end Collatz.Research.FirstDescent.Batch229
