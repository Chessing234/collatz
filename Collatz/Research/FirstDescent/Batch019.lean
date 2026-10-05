import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 19. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch019
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 839). -/
theorem data_15_839 : oddCount 839 15 = 9 ∧
    acceleratedOrbit 15 839 = 505 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_839 : ∀ j : Fin 15,
    839 ≤ acceleratedOrbit j.val 839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_839 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 839) = 19683 * m + 505 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 839
  rw [data_15_839.1, data_15_839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_839 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 839) < 32768 * m + 839 := by
  apply descent_of_endpoint
  · rw [data_15_839.1]; exact data_15_839.2.2
  · rw [data_15_839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 1095). -/
theorem data_15_1095 : oddCount 1095 15 = 9 ∧
    acceleratedOrbit 15 1095 = 659 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_1095 : ∀ j : Fin 15,
    1095 ≤ acceleratedOrbit j.val 1095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_1095 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1095) = 19683 * m + 659 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 1095
  rw [data_15_1095.1, data_15_1095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_1095 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1095) < 32768 * m + 1095 := by
  apply descent_of_endpoint
  · rw [data_15_1095.1]; exact data_15_1095.2.2
  · rw [data_15_1095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 1151). -/
theorem data_15_1151 : oddCount 1151 15 = 9 ∧
    acceleratedOrbit 15 1151 = 692 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_1151 : ∀ j : Fin 15,
    1151 ≤ acceleratedOrbit j.val 1151 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_1151 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1151) = 19683 * m + 692 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 1151
  rw [data_15_1151.1, data_15_1151.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_1151 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1151) < 32768 * m + 1151 := by
  apply descent_of_endpoint
  · rw [data_15_1151.1]; exact data_15_1151.2.2
  · rw [data_15_1151.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 1275). -/
theorem data_15_1275 : oddCount 1275 15 = 9 ∧
    acceleratedOrbit 15 1275 = 767 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_1275 : ∀ j : Fin 15,
    1275 ≤ acceleratedOrbit j.val 1275 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_1275 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1275) = 19683 * m + 767 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 1275
  rw [data_15_1275.1, data_15_1275.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_1275 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1275) < 32768 * m + 1275 := by
  apply descent_of_endpoint
  · rw [data_15_1275.1]; exact data_15_1275.2.2
  · rw [data_15_1275.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 1775). -/
theorem data_15_1775 : oddCount 1775 15 = 9 ∧
    acceleratedOrbit 15 1775 = 1067 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_1775 : ∀ j : Fin 15,
    1775 ≤ acceleratedOrbit j.val 1775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_1775 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1775) = 19683 * m + 1067 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 1775
  rw [data_15_1775.1, data_15_1775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_1775 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1775) < 32768 * m + 1775 := by
  apply descent_of_endpoint
  · rw [data_15_1775.1]; exact data_15_1775.2.2
  · rw [data_15_1775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 1903). -/
theorem data_15_1903 : oddCount 1903 15 = 9 ∧
    acceleratedOrbit 15 1903 = 1144 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_1903 : ∀ j : Fin 15,
    1903 ≤ acceleratedOrbit j.val 1903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_1903 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1903) = 19683 * m + 1144 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 1903
  rw [data_15_1903.1, data_15_1903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_1903 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 1903) < 32768 * m + 1903 := by
  apply descent_of_endpoint
  · rw [data_15_1903.1]; exact data_15_1903.2.2
  · rw [data_15_1903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2119). -/
theorem data_15_2119 : oddCount 2119 15 = 9 ∧
    acceleratedOrbit 15 2119 = 1274 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2119 : ∀ j : Fin 15,
    2119 ≤ acceleratedOrbit j.val 2119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2119 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2119) = 19683 * m + 1274 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2119
  rw [data_15_2119.1, data_15_2119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2119 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2119) < 32768 * m + 2119 := by
  apply descent_of_endpoint
  · rw [data_15_2119.1]; exact data_15_2119.2.2
  · rw [data_15_2119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 2279). -/
theorem data_15_2279 : oddCount 2279 15 = 9 ∧
    acceleratedOrbit 15 2279 = 1370 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_2279 : ∀ j : Fin 15,
    2279 ≤ acceleratedOrbit j.val 2279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_2279 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2279) = 19683 * m + 1370 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 2279
  rw [data_15_2279.1, data_15_2279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_2279 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 2279) < 32768 * m + 2279 := by
  apply descent_of_endpoint
  · rw [data_15_2279.1]; exact data_15_2279.2.2
  · rw [data_15_2279.2.1]; decide

end Collatz.Research.FirstDescent.Batch019
