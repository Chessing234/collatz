import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 27. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch027
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 12143). -/
theorem data_15_12143 : oddCount 12143 15 = 9 ∧
    acceleratedOrbit 15 12143 = 7295 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_12143 : ∀ j : Fin 15,
    12143 ≤ acceleratedOrbit j.val 12143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_12143 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12143) = 19683 * m + 7295 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 12143
  rw [data_15_12143.1, data_15_12143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_12143 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12143) < 32768 * m + 12143 := by
  apply descent_of_endpoint
  · rw [data_15_12143.1]; exact data_15_12143.2.2
  · rw [data_15_12143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 12511). -/
theorem data_15_12511 : oddCount 12511 15 = 9 ∧
    acceleratedOrbit 15 12511 = 7516 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_12511 : ∀ j : Fin 15,
    12511 ≤ acceleratedOrbit j.val 12511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_12511 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12511) = 19683 * m + 7516 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 12511
  rw [data_15_12511.1, data_15_12511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_12511 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12511) < 32768 * m + 12511 := by
  apply descent_of_endpoint
  · rw [data_15_12511.1]; exact data_15_12511.2.2
  · rw [data_15_12511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 12543). -/
theorem data_15_12543 : oddCount 12543 15 = 9 ∧
    acceleratedOrbit 15 12543 = 7535 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_12543 : ∀ j : Fin 15,
    12543 ≤ acceleratedOrbit j.val 12543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_12543 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12543) = 19683 * m + 7535 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 12543
  rw [data_15_12543.1, data_15_12543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_12543 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12543) < 32768 * m + 12543 := by
  apply descent_of_endpoint
  · rw [data_15_12543.1]; exact data_15_12543.2.2
  · rw [data_15_12543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 12571). -/
theorem data_15_12571 : oddCount 12571 15 = 9 ∧
    acceleratedOrbit 15 12571 = 7552 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_12571 : ∀ j : Fin 15,
    12571 ≤ acceleratedOrbit j.val 12571 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_12571 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12571) = 19683 * m + 7552 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 12571
  rw [data_15_12571.1, data_15_12571.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_12571 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12571) < 32768 * m + 12571 := by
  apply descent_of_endpoint
  · rw [data_15_12571.1]; exact data_15_12571.2.2
  · rw [data_15_12571.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 12827). -/
theorem data_15_12827 : oddCount 12827 15 = 9 ∧
    acceleratedOrbit 15 12827 = 7706 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_12827 : ∀ j : Fin 15,
    12827 ≤ acceleratedOrbit j.val 12827 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_12827 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12827) = 19683 * m + 7706 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 12827
  rw [data_15_12827.1, data_15_12827.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_12827 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12827) < 32768 * m + 12827 := by
  apply descent_of_endpoint
  · rw [data_15_12827.1]; exact data_15_12827.2.2
  · rw [data_15_12827.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 12967). -/
theorem data_15_12967 : oddCount 12967 15 = 9 ∧
    acceleratedOrbit 15 12967 = 7790 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_12967 : ∀ j : Fin 15,
    12967 ≤ acceleratedOrbit j.val 12967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_12967 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12967) = 19683 * m + 7790 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 12967
  rw [data_15_12967.1, data_15_12967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_12967 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 12967) < 32768 * m + 12967 := by
  apply descent_of_endpoint
  · rw [data_15_12967.1]; exact data_15_12967.2.2
  · rw [data_15_12967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 13007). -/
theorem data_15_13007 : oddCount 13007 15 = 9 ∧
    acceleratedOrbit 15 13007 = 7814 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_13007 : ∀ j : Fin 15,
    13007 ≤ acceleratedOrbit j.val 13007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_13007 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13007) = 19683 * m + 7814 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 13007
  rw [data_15_13007.1, data_15_13007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_13007 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13007) < 32768 * m + 13007 := by
  apply descent_of_endpoint
  · rw [data_15_13007.1]; exact data_15_13007.2.2
  · rw [data_15_13007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 13087). -/
theorem data_15_13087 : oddCount 13087 15 = 9 ∧
    acceleratedOrbit 15 13087 = 7862 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_13087 : ∀ j : Fin 15,
    13087 ≤ acceleratedOrbit j.val 13087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_13087 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13087) = 19683 * m + 7862 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 13087
  rw [data_15_13087.1, data_15_13087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_13087 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13087) < 32768 * m + 13087 := by
  apply descent_of_endpoint
  · rw [data_15_13087.1]; exact data_15_13087.2.2
  · rw [data_15_13087.2.1]; decide

end Collatz.Research.FirstDescent.Batch027
