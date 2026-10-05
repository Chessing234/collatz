import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 20. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch020
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2299). -/
theorem data_15_2299 : oddCount 2299 15 = 9 ∧
    acceleratedOrbit 15 2299 = 1382 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2299 : ∀ j : Fin 15,
    2299 ≤ acceleratedOrbit j.val 2299 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2299 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2299) = 19683 * m + 1382 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2299
  rw [data_15_2299.1, data_15_2299.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2299 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2299) < 32768 * m + 2299 := by
  apply descent_of_endpoint
  · rw [data_15_2299.1]; exact data_15_2299.2.2
  · rw [data_15_2299.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2303). -/
theorem data_15_2303 : oddCount 2303 15 = 9 ∧
    acceleratedOrbit 15 2303 = 1384 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2303 : ∀ j : Fin 15,
    2303 ≤ acceleratedOrbit j.val 2303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2303 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2303) = 19683 * m + 1384 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2303
  rw [data_15_2303.1, data_15_2303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2303 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2303) < 32768 * m + 2303 := by
  apply descent_of_endpoint
  · rw [data_15_2303.1]; exact data_15_2303.2.2
  · rw [data_15_2303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2719). -/
theorem data_15_2719 : oddCount 2719 15 = 9 ∧
    acceleratedOrbit 15 2719 = 1634 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2719 : ∀ j : Fin 15,
    2719 ≤ acceleratedOrbit j.val 2719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2719 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2719) = 19683 * m + 1634 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2719
  rw [data_15_2719.1, data_15_2719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2719 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2719) < 32768 * m + 2719 := by
  apply descent_of_endpoint
  · rw [data_15_2719.1]; exact data_15_2719.2.2
  · rw [data_15_2719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2727). -/
theorem data_15_2727 : oddCount 2727 15 = 9 ∧
    acceleratedOrbit 15 2727 = 1639 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2727 : ∀ j : Fin 15,
    2727 ≤ acceleratedOrbit j.val 2727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2727 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2727) = 19683 * m + 1639 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2727
  rw [data_15_2727.1, data_15_2727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2727 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2727) < 32768 * m + 2727 := by
  apply descent_of_endpoint
  · rw [data_15_2727.1]; exact data_15_2727.2.2
  · rw [data_15_2727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2767). -/
theorem data_15_2767 : oddCount 2767 15 = 9 ∧
    acceleratedOrbit 15 2767 = 1663 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2767 : ∀ j : Fin 15,
    2767 ≤ acceleratedOrbit j.val 2767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2767 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2767) = 19683 * m + 1663 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2767
  rw [data_15_2767.1, data_15_2767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2767 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2767) < 32768 * m + 2767 := by
  apply descent_of_endpoint
  · rw [data_15_2767.1]; exact data_15_2767.2.2
  · rw [data_15_2767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2799). -/
theorem data_15_2799 : oddCount 2799 15 = 9 ∧
    acceleratedOrbit 15 2799 = 1682 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2799 : ∀ j : Fin 15,
    2799 ≤ acceleratedOrbit j.val 2799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2799 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2799) = 19683 * m + 1682 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2799
  rw [data_15_2799.1, data_15_2799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2799 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2799) < 32768 * m + 2799 := by
  apply descent_of_endpoint
  · rw [data_15_2799.1]; exact data_15_2799.2.2
  · rw [data_15_2799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2847). -/
theorem data_15_2847 : oddCount 2847 15 = 9 ∧
    acceleratedOrbit 15 2847 = 1711 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2847 : ∀ j : Fin 15,
    2847 ≤ acceleratedOrbit j.val 2847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2847 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2847) = 19683 * m + 1711 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2847
  rw [data_15_2847.1, data_15_2847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2847 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2847) < 32768 * m + 2847 := by
  apply descent_of_endpoint
  · rw [data_15_2847.1]; exact data_15_2847.2.2
  · rw [data_15_2847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2983). -/
theorem data_15_2983 : oddCount 2983 15 = 9 ∧
    acceleratedOrbit 15 2983 = 1793 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2983 : ∀ j : Fin 15,
    2983 ≤ acceleratedOrbit j.val 2983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2983 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2983) = 19683 * m + 1793 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2983
  rw [data_15_2983.1, data_15_2983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2983 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2983) < 32768 * m + 2983 := by
  apply descent_of_endpoint
  · rw [data_15_2983.1]; exact data_15_2983.2.2
  · rw [data_15_2983.2.1]; decide

end Collatz.Research.FirstDescent.Batch020
