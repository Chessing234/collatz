import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 271. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch271
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 152423). -/
theorem data_20_152423 : oddCount 152423 20 = 12 ∧
    acceleratedOrbit 20 152423 = 77252 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_152423 : ∀ j : Fin 20,
    152423 ≤ acceleratedOrbit j.val 152423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_152423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 152423) = 531441 * m + 77252 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 152423
  rw [data_20_152423.1, data_20_152423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_152423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 152423) < 1048576 * m + 152423 := by
  apply descent_of_endpoint
  · rw [data_20_152423.1]; exact data_20_152423.2.2
  · rw [data_20_152423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 153115). -/
theorem data_20_153115 : oddCount 153115 20 = 12 ∧
    acceleratedOrbit 20 153115 = 77603 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_153115 : ∀ j : Fin 20,
    153115 ≤ acceleratedOrbit j.val 153115 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_153115 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 153115) = 531441 * m + 77603 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 153115
  rw [data_20_153115.1, data_20_153115.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_153115 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 153115) < 1048576 * m + 153115 := by
  apply descent_of_endpoint
  · rw [data_20_153115.1]; exact data_20_153115.2.2
  · rw [data_20_153115.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 153711). -/
theorem data_20_153711 : oddCount 153711 20 = 12 ∧
    acceleratedOrbit 20 153711 = 77905 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_153711 : ∀ j : Fin 20,
    153711 ≤ acceleratedOrbit j.val 153711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_153711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 153711) = 531441 * m + 77905 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 153711
  rw [data_20_153711.1, data_20_153711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_153711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 153711) < 1048576 * m + 153711 := by
  apply descent_of_endpoint
  · rw [data_20_153711.1]; exact data_20_153711.2.2
  · rw [data_20_153711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 154607). -/
theorem data_20_154607 : oddCount 154607 20 = 12 ∧
    acceleratedOrbit 20 154607 = 78359 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_154607 : ∀ j : Fin 20,
    154607 ≤ acceleratedOrbit j.val 154607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_154607 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 154607) = 531441 * m + 78359 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 154607
  rw [data_20_154607.1, data_20_154607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_154607 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 154607) < 1048576 * m + 154607 := by
  apply descent_of_endpoint
  · rw [data_20_154607.1]; exact data_20_154607.2.2
  · rw [data_20_154607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 155495). -/
theorem data_20_155495 : oddCount 155495 20 = 12 ∧
    acceleratedOrbit 20 155495 = 78809 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_155495 : ∀ j : Fin 20,
    155495 ≤ acceleratedOrbit j.val 155495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_155495 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 155495) = 531441 * m + 78809 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 155495
  rw [data_20_155495.1, data_20_155495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_155495 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 155495) < 1048576 * m + 155495 := by
  apply descent_of_endpoint
  · rw [data_20_155495.1]; exact data_20_155495.2.2
  · rw [data_20_155495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 155807). -/
theorem data_20_155807 : oddCount 155807 20 = 12 ∧
    acceleratedOrbit 20 155807 = 78967 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_155807 : ∀ j : Fin 20,
    155807 ≤ acceleratedOrbit j.val 155807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_155807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 155807) = 531441 * m + 78967 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 155807
  rw [data_20_155807.1, data_20_155807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_155807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 155807) < 1048576 * m + 155807 := by
  apply descent_of_endpoint
  · rw [data_20_155807.1]; exact data_20_155807.2.2
  · rw [data_20_155807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 156063). -/
theorem data_20_156063 : oddCount 156063 20 = 12 ∧
    acceleratedOrbit 20 156063 = 79097 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_156063 : ∀ j : Fin 20,
    156063 ≤ acceleratedOrbit j.val 156063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_156063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 156063) = 531441 * m + 79097 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 156063
  rw [data_20_156063.1, data_20_156063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_156063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 156063) < 1048576 * m + 156063 := by
  apply descent_of_endpoint
  · rw [data_20_156063.1]; exact data_20_156063.2.2
  · rw [data_20_156063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 156519). -/
theorem data_20_156519 : oddCount 156519 20 = 12 ∧
    acceleratedOrbit 20 156519 = 79328 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_156519 : ∀ j : Fin 20,
    156519 ≤ acceleratedOrbit j.val 156519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_156519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 156519) = 531441 * m + 79328 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 156519
  rw [data_20_156519.1, data_20_156519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_156519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 156519) < 1048576 * m + 156519 := by
  apply descent_of_endpoint
  · rw [data_20_156519.1]; exact data_20_156519.2.2
  · rw [data_20_156519.2.1]; decide

end Collatz.Research.FirstDescent.Batch271
