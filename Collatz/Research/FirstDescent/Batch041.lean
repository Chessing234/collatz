import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 41. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch041
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 1183). -/
theorem data_16_1183 : oddCount 1183 16 = 10 ∧
    acceleratedOrbit 16 1183 = 1067 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_1183 : ∀ j : Fin 16,
    1183 ≤ acceleratedOrbit j.val 1183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_1183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1183) = 59049 * m + 1067 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 1183
  rw [data_16_1183.1, data_16_1183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_1183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1183) < 65536 * m + 1183 := by
  apply descent_of_endpoint
  · rw [data_16_1183.1]; exact data_16_1183.2.2
  · rw [data_16_1183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 1351). -/
theorem data_16_1351 : oddCount 1351 16 = 10 ∧
    acceleratedOrbit 16 1351 = 1219 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_1351 : ∀ j : Fin 16,
    1351 ≤ acceleratedOrbit j.val 1351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_1351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1351) = 59049 * m + 1219 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 1351
  rw [data_16_1351.1, data_16_1351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_1351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1351) < 65536 * m + 1351 := by
  apply descent_of_endpoint
  · rw [data_16_1351.1]; exact data_16_1351.2.2
  · rw [data_16_1351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 1519). -/
theorem data_16_1519 : oddCount 1519 16 = 10 ∧
    acceleratedOrbit 16 1519 = 1370 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_1519 : ∀ j : Fin 16,
    1519 ≤ acceleratedOrbit j.val 1519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_1519 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1519) = 59049 * m + 1370 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 1519
  rw [data_16_1519.1, data_16_1519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_1519 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1519) < 65536 * m + 1519 := by
  apply descent_of_endpoint
  · rw [data_16_1519.1]; exact data_16_1519.2.2
  · rw [data_16_1519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 1535). -/
theorem data_16_1535 : oddCount 1535 16 = 10 ∧
    acceleratedOrbit 16 1535 = 1384 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_1535 : ∀ j : Fin 16,
    1535 ≤ acceleratedOrbit j.val 1535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_1535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1535) = 59049 * m + 1384 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 1535
  rw [data_16_1535.1, data_16_1535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_1535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1535) < 65536 * m + 1535 := by
  apply descent_of_endpoint
  · rw [data_16_1535.1]; exact data_16_1535.2.2
  · rw [data_16_1535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 1627). -/
theorem data_16_1627 : oddCount 1627 16 = 10 ∧
    acceleratedOrbit 16 1627 = 1468 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_1627 : ∀ j : Fin 16,
    1627 ≤ acceleratedOrbit j.val 1627 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_1627 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1627) = 59049 * m + 1468 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 1627
  rw [data_16_1627.1, data_16_1627.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_1627 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1627) < 65536 * m + 1627 := by
  apply descent_of_endpoint
  · rw [data_16_1627.1]; exact data_16_1627.2.2
  · rw [data_16_1627.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2367). -/
theorem data_16_2367 : oddCount 2367 16 = 10 ∧
    acceleratedOrbit 16 2367 = 2134 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2367 : ∀ j : Fin 16,
    2367 ≤ acceleratedOrbit j.val 2367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2367 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2367) = 59049 * m + 2134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2367
  rw [data_16_2367.1, data_16_2367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2367 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2367) < 65536 * m + 2367 := by
  apply descent_of_endpoint
  · rw [data_16_2367.1]; exact data_16_2367.2.2
  · rw [data_16_2367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2407). -/
theorem data_16_2407 : oddCount 2407 16 = 10 ∧
    acceleratedOrbit 16 2407 = 2170 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2407 : ∀ j : Fin 16,
    2407 ≤ acceleratedOrbit j.val 2407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2407) = 59049 * m + 2170 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2407
  rw [data_16_2407.1, data_16_2407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2407) < 65536 * m + 2407 := by
  apply descent_of_endpoint
  · rw [data_16_2407.1]; exact data_16_2407.2.2
  · rw [data_16_2407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2495). -/
theorem data_16_2495 : oddCount 2495 16 = 10 ∧
    acceleratedOrbit 16 2495 = 2249 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2495 : ∀ j : Fin 16,
    2495 ≤ acceleratedOrbit j.val 2495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2495) = 59049 * m + 2249 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2495
  rw [data_16_2495.1, data_16_2495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2495) < 65536 * m + 2495 := by
  apply descent_of_endpoint
  · rw [data_16_2495.1]; exact data_16_2495.2.2
  · rw [data_16_2495.2.1]; decide

end Collatz.Research.FirstDescent.Batch041
