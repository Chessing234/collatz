import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 270. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch270
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 150639). -/
theorem data_20_150639 : oddCount 150639 20 = 12 ∧
    acceleratedOrbit 20 150639 = 76348 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_150639 : ∀ j : Fin 20,
    150639 ≤ acceleratedOrbit j.val 150639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_150639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150639) = 531441 * m + 76348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 150639
  rw [data_20_150639.1, data_20_150639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_150639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150639) < 1048576 * m + 150639 := by
  apply descent_of_endpoint
  · rw [data_20_150639.1]; exact data_20_150639.2.2
  · rw [data_20_150639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 150735). -/
theorem data_20_150735 : oddCount 150735 20 = 12 ∧
    acceleratedOrbit 20 150735 = 76397 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_150735 : ∀ j : Fin 20,
    150735 ≤ acceleratedOrbit j.val 150735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_150735 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150735) = 531441 * m + 76397 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 150735
  rw [data_20_150735.1, data_20_150735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_150735 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150735) < 1048576 * m + 150735 := by
  apply descent_of_endpoint
  · rw [data_20_150735.1]; exact data_20_150735.2.2
  · rw [data_20_150735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 150943). -/
theorem data_20_150943 : oddCount 150943 20 = 12 ∧
    acceleratedOrbit 20 150943 = 76502 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_150943 : ∀ j : Fin 20,
    150943 ≤ acceleratedOrbit j.val 150943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_150943 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150943) = 531441 * m + 76502 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 150943
  rw [data_20_150943.1, data_20_150943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_150943 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150943) < 1048576 * m + 150943 := by
  apply descent_of_endpoint
  · rw [data_20_150943.1]; exact data_20_150943.2.2
  · rw [data_20_150943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 151463). -/
theorem data_20_151463 : oddCount 151463 20 = 12 ∧
    acceleratedOrbit 20 151463 = 76766 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_151463 : ∀ j : Fin 20,
    151463 ≤ acceleratedOrbit j.val 151463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_151463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 151463) = 531441 * m + 76766 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 151463
  rw [data_20_151463.1, data_20_151463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_151463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 151463) < 1048576 * m + 151463 := by
  apply descent_of_endpoint
  · rw [data_20_151463.1]; exact data_20_151463.2.2
  · rw [data_20_151463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 151623). -/
theorem data_20_151623 : oddCount 151623 20 = 12 ∧
    acceleratedOrbit 20 151623 = 76847 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_151623 : ∀ j : Fin 20,
    151623 ≤ acceleratedOrbit j.val 151623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_151623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 151623) = 531441 * m + 76847 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 151623
  rw [data_20_151623.1, data_20_151623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_151623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 151623) < 1048576 * m + 151623 := by
  apply descent_of_endpoint
  · rw [data_20_151623.1]; exact data_20_151623.2.2
  · rw [data_20_151623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 151711). -/
theorem data_20_151711 : oddCount 151711 20 = 12 ∧
    acceleratedOrbit 20 151711 = 76891 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_151711 : ∀ j : Fin 20,
    151711 ≤ acceleratedOrbit j.val 151711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_151711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 151711) = 531441 * m + 76891 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 151711
  rw [data_20_151711.1, data_20_151711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_151711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 151711) < 1048576 * m + 151711 := by
  apply descent_of_endpoint
  · rw [data_20_151711.1]; exact data_20_151711.2.2
  · rw [data_20_151711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 152231). -/
theorem data_20_152231 : oddCount 152231 20 = 12 ∧
    acceleratedOrbit 20 152231 = 77155 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_152231 : ∀ j : Fin 20,
    152231 ≤ acceleratedOrbit j.val 152231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_152231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 152231) = 531441 * m + 77155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 152231
  rw [data_20_152231.1, data_20_152231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_152231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 152231) < 1048576 * m + 152231 := by
  apply descent_of_endpoint
  · rw [data_20_152231.1]; exact data_20_152231.2.2
  · rw [data_20_152231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 152391). -/
theorem data_20_152391 : oddCount 152391 20 = 12 ∧
    acceleratedOrbit 20 152391 = 77236 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_152391 : ∀ j : Fin 20,
    152391 ≤ acceleratedOrbit j.val 152391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_152391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 152391) = 531441 * m + 77236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 152391
  rw [data_20_152391.1, data_20_152391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_152391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 152391) < 1048576 * m + 152391 := by
  apply descent_of_endpoint
  · rw [data_20_152391.1]; exact data_20_152391.2.2
  · rw [data_20_152391.2.1]; decide

end Collatz.Research.FirstDescent.Batch270
