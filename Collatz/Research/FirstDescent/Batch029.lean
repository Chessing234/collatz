import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 29. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch029
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 15295). -/
theorem data_15_15295 : oddCount 15295 15 = 9 ∧
    acceleratedOrbit 15 15295 = 9188 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_15295 : ∀ j : Fin 15,
    15295 ≤ acceleratedOrbit j.val 15295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_15295 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15295) = 19683 * m + 9188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 15295
  rw [data_15_15295.1, data_15_15295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_15295 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15295) < 32768 * m + 15295 := by
  apply descent_of_endpoint
  · rw [data_15_15295.1]; exact data_15_15295.2.2
  · rw [data_15_15295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 15343). -/
theorem data_15_15343 : oddCount 15343 15 = 9 ∧
    acceleratedOrbit 15 15343 = 9217 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_15343 : ∀ j : Fin 15,
    15343 ≤ acceleratedOrbit j.val 15343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_15343 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15343) = 19683 * m + 9217 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 15343
  rw [data_15_15343.1, data_15_15343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_15343 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15343) < 32768 * m + 15343 := by
  apply descent_of_endpoint
  · rw [data_15_15343.1]; exact data_15_15343.2.2
  · rw [data_15_15343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 15839). -/
theorem data_15_15839 : oddCount 15839 15 = 9 ∧
    acceleratedOrbit 15 15839 = 9515 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_15839 : ∀ j : Fin 15,
    15839 ≤ acceleratedOrbit j.val 15839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_15839 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15839) = 19683 * m + 9515 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 15839
  rw [data_15_15839.1, data_15_15839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_15839 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15839) < 32768 * m + 15839 := by
  apply descent_of_endpoint
  · rw [data_15_15839.1]; exact data_15_15839.2.2
  · rw [data_15_15839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 15919). -/
theorem data_15_15919 : oddCount 15919 15 = 9 ∧
    acceleratedOrbit 15 15919 = 9563 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_15919 : ∀ j : Fin 15,
    15919 ≤ acceleratedOrbit j.val 15919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_15919 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15919) = 19683 * m + 9563 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 15919
  rw [data_15_15919.1, data_15_15919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_15919 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 15919) < 32768 * m + 15919 := by
  apply descent_of_endpoint
  · rw [data_15_15919.1]; exact data_15_15919.2.2
  · rw [data_15_15919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 16027). -/
theorem data_15_16027 : oddCount 16027 15 = 9 ∧
    acceleratedOrbit 15 16027 = 9628 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_16027 : ∀ j : Fin 15,
    16027 ≤ acceleratedOrbit j.val 16027 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_16027 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16027) = 19683 * m + 9628 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 16027
  rw [data_15_16027.1, data_15_16027.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_16027 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16027) < 32768 * m + 16027 := by
  apply descent_of_endpoint
  · rw [data_15_16027.1]; exact data_15_16027.2.2
  · rw [data_15_16027.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 16123). -/
theorem data_15_16123 : oddCount 16123 15 = 9 ∧
    acceleratedOrbit 15 16123 = 9686 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_16123 : ∀ j : Fin 15,
    16123 ≤ acceleratedOrbit j.val 16123 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_16123 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16123) = 19683 * m + 9686 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 16123
  rw [data_15_16123.1, data_15_16123.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_16123 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16123) < 32768 * m + 16123 := by
  apply descent_of_endpoint
  · rw [data_15_16123.1]; exact data_15_16123.2.2
  · rw [data_15_16123.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 16287). -/
theorem data_15_16287 : oddCount 16287 15 = 9 ∧
    acceleratedOrbit 15 16287 = 9784 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_16287 : ∀ j : Fin 15,
    16287 ≤ acceleratedOrbit j.val 16287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_16287 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16287) = 19683 * m + 9784 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 16287
  rw [data_15_16287.1, data_15_16287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_16287 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16287) < 32768 * m + 16287 := by
  apply descent_of_endpoint
  · rw [data_15_16287.1]; exact data_15_16287.2.2
  · rw [data_15_16287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 16743). -/
theorem data_15_16743 : oddCount 16743 15 = 9 ∧
    acceleratedOrbit 15 16743 = 10058 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_16743 : ∀ j : Fin 15,
    16743 ≤ acceleratedOrbit j.val 16743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_16743 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16743) = 19683 * m + 10058 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 16743
  rw [data_15_16743.1, data_15_16743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_16743 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 16743) < 32768 * m + 16743 := by
  apply descent_of_endpoint
  · rw [data_15_16743.1]; exact data_15_16743.2.2
  · rw [data_15_16743.2.1]; decide

end Collatz.Research.FirstDescent.Batch029
