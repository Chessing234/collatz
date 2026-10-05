import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 33. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch033
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 21727). -/
theorem data_15_21727 : oddCount 21727 15 = 9 ∧
    acceleratedOrbit 15 21727 = 13052 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_21727 : ∀ j : Fin 15,
    21727 ≤ acceleratedOrbit j.val 21727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_21727 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21727) = 19683 * m + 13052 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 21727
  rw [data_15_21727.1, data_15_21727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_21727 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21727) < 32768 * m + 21727 := by
  apply descent_of_endpoint
  · rw [data_15_21727.1]; exact data_15_21727.2.2
  · rw [data_15_21727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 21807). -/
theorem data_15_21807 : oddCount 21807 15 = 9 ∧
    acceleratedOrbit 15 21807 = 13100 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_21807 : ∀ j : Fin 15,
    21807 ≤ acceleratedOrbit j.val 21807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_21807 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21807) = 19683 * m + 13100 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 21807
  rw [data_15_21807.1, data_15_21807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_21807 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 21807) < 32768 * m + 21807 := by
  apply descent_of_endpoint
  · rw [data_15_21807.1]; exact data_15_21807.2.2
  · rw [data_15_21807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 22047). -/
theorem data_15_22047 : oddCount 22047 15 = 9 ∧
    acceleratedOrbit 15 22047 = 13244 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_22047 : ∀ j : Fin 15,
    22047 ≤ acceleratedOrbit j.val 22047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_22047 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22047) = 19683 * m + 13244 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 22047
  rw [data_15_22047.1, data_15_22047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_22047 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22047) < 32768 * m + 22047 := by
  apply descent_of_endpoint
  · rw [data_15_22047.1]; exact data_15_22047.2.2
  · rw [data_15_22047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 22207). -/
theorem data_15_22207 : oddCount 22207 15 = 9 ∧
    acceleratedOrbit 15 22207 = 13340 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_22207 : ∀ j : Fin 15,
    22207 ≤ acceleratedOrbit j.val 22207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_22207 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22207) = 19683 * m + 13340 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 22207
  rw [data_15_22207.1, data_15_22207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_22207 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22207) < 32768 * m + 22207 := by
  apply descent_of_endpoint
  · rw [data_15_22207.1]; exact data_15_22207.2.2
  · rw [data_15_22207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 22655). -/
theorem data_15_22655 : oddCount 22655 15 = 9 ∧
    acceleratedOrbit 15 22655 = 13609 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_22655 : ∀ j : Fin 15,
    22655 ≤ acceleratedOrbit j.val 22655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_22655 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22655) = 19683 * m + 13609 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 22655
  rw [data_15_22655.1, data_15_22655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_22655 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22655) < 32768 * m + 22655 := by
  apply descent_of_endpoint
  · rw [data_15_22655.1]; exact data_15_22655.2.2
  · rw [data_15_22655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 22751). -/
theorem data_15_22751 : oddCount 22751 15 = 9 ∧
    acceleratedOrbit 15 22751 = 13667 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_22751 : ∀ j : Fin 15,
    22751 ≤ acceleratedOrbit j.val 22751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_22751 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22751) = 19683 * m + 13667 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 22751
  rw [data_15_22751.1, data_15_22751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_22751 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22751) < 32768 * m + 22751 := by
  apply descent_of_endpoint
  · rw [data_15_22751.1]; exact data_15_22751.2.2
  · rw [data_15_22751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 22811). -/
theorem data_15_22811 : oddCount 22811 15 = 9 ∧
    acceleratedOrbit 15 22811 = 13703 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_22811 : ∀ j : Fin 15,
    22811 ≤ acceleratedOrbit j.val 22811 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_22811 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22811) = 19683 * m + 13703 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 22811
  rw [data_15_22811.1, data_15_22811.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_22811 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22811) < 32768 * m + 22811 := by
  apply descent_of_endpoint
  · rw [data_15_22811.1]; exact data_15_22811.2.2
  · rw [data_15_22811.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 22911). -/
theorem data_15_22911 : oddCount 22911 15 = 9 ∧
    acceleratedOrbit 15 22911 = 13763 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_22911 : ∀ j : Fin 15,
    22911 ≤ acceleratedOrbit j.val 22911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_22911 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22911) = 19683 * m + 13763 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 22911
  rw [data_15_22911.1, data_15_22911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_22911 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 22911) < 32768 * m + 22911 := by
  apply descent_of_endpoint
  · rw [data_15_22911.1]; exact data_15_22911.2.2
  · rw [data_15_22911.2.1]; decide

end Collatz.Research.FirstDescent.Batch033
