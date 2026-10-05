import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 260. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch260
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 116191). -/
theorem data_20_116191 : oddCount 116191 20 = 12 ∧
    acceleratedOrbit 20 116191 = 58889 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_116191 : ∀ j : Fin 20,
    116191 ≤ acceleratedOrbit j.val 116191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_116191 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 116191) = 531441 * m + 58889 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 116191
  rw [data_20_116191.1, data_20_116191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_116191 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 116191) < 1048576 * m + 116191 := by
  apply descent_of_endpoint
  · rw [data_20_116191.1]; exact data_20_116191.2.2
  · rw [data_20_116191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 116463). -/
theorem data_20_116463 : oddCount 116463 20 = 12 ∧
    acceleratedOrbit 20 116463 = 59027 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_116463 : ∀ j : Fin 20,
    116463 ≤ acceleratedOrbit j.val 116463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_116463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 116463) = 531441 * m + 59027 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 116463
  rw [data_20_116463.1, data_20_116463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_116463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 116463) < 1048576 * m + 116463 := by
  apply descent_of_endpoint
  · rw [data_20_116463.1]; exact data_20_116463.2.2
  · rw [data_20_116463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 117231). -/
theorem data_20_117231 : oddCount 117231 20 = 12 ∧
    acceleratedOrbit 20 117231 = 59416 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_117231 : ∀ j : Fin 20,
    117231 ≤ acceleratedOrbit j.val 117231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_117231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 117231) = 531441 * m + 59416 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 117231
  rw [data_20_117231.1, data_20_117231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_117231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 117231) < 1048576 * m + 117231 := by
  apply descent_of_endpoint
  · rw [data_20_117231.1]; exact data_20_117231.2.2
  · rw [data_20_117231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 117695). -/
theorem data_20_117695 : oddCount 117695 20 = 12 ∧
    acceleratedOrbit 20 117695 = 59651 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_117695 : ∀ j : Fin 20,
    117695 ≤ acceleratedOrbit j.val 117695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_117695 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 117695) = 531441 * m + 59651 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 117695
  rw [data_20_117695.1, data_20_117695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_117695 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 117695) < 1048576 * m + 117695 := by
  apply descent_of_endpoint
  · rw [data_20_117695.1]; exact data_20_117695.2.2
  · rw [data_20_117695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 118119). -/
theorem data_20_118119 : oddCount 118119 20 = 12 ∧
    acceleratedOrbit 20 118119 = 59866 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_118119 : ∀ j : Fin 20,
    118119 ≤ acceleratedOrbit j.val 118119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_118119 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 118119) = 531441 * m + 59866 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 118119
  rw [data_20_118119.1, data_20_118119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_118119 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 118119) < 1048576 * m + 118119 := by
  apply descent_of_endpoint
  · rw [data_20_118119.1]; exact data_20_118119.2.2
  · rw [data_20_118119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 119387). -/
theorem data_20_119387 : oddCount 119387 20 = 12 ∧
    acceleratedOrbit 20 119387 = 60509 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_119387 : ∀ j : Fin 20,
    119387 ≤ acceleratedOrbit j.val 119387 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_119387 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 119387) = 531441 * m + 60509 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 119387
  rw [data_20_119387.1, data_20_119387.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_119387 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 119387) < 1048576 * m + 119387 := by
  apply descent_of_endpoint
  · rw [data_20_119387.1]; exact data_20_119387.2.2
  · rw [data_20_119387.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 120167). -/
theorem data_20_120167 : oddCount 120167 20 = 12 ∧
    acceleratedOrbit 20 120167 = 60904 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_120167 : ∀ j : Fin 20,
    120167 ≤ acceleratedOrbit j.val 120167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_120167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 120167) = 531441 * m + 60904 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 120167
  rw [data_20_120167.1, data_20_120167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_120167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 120167) < 1048576 * m + 120167 := by
  apply descent_of_endpoint
  · rw [data_20_120167.1]; exact data_20_120167.2.2
  · rw [data_20_120167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 120423). -/
theorem data_20_120423 : oddCount 120423 20 = 12 ∧
    acceleratedOrbit 20 120423 = 61034 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_120423 : ∀ j : Fin 20,
    120423 ≤ acceleratedOrbit j.val 120423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_120423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 120423) = 531441 * m + 61034 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 120423
  rw [data_20_120423.1, data_20_120423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_120423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 120423) < 1048576 * m + 120423 := by
  apply descent_of_endpoint
  · rw [data_20_120423.1]; exact data_20_120423.2.2
  · rw [data_20_120423.2.1]; decide

end Collatz.Research.FirstDescent.Batch260
