import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 259. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch259
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 113119). -/
theorem data_20_113119 : oddCount 113119 20 = 12 ∧
    acceleratedOrbit 20 113119 = 57332 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_113119 : ∀ j : Fin 20,
    113119 ≤ acceleratedOrbit j.val 113119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_113119 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 113119) = 531441 * m + 57332 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 113119
  rw [data_20_113119.1, data_20_113119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_113119 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 113119) < 1048576 * m + 113119 := by
  apply descent_of_endpoint
  · rw [data_20_113119.1]; exact data_20_113119.2.2
  · rw [data_20_113119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 113135). -/
theorem data_20_113135 : oddCount 113135 20 = 12 ∧
    acceleratedOrbit 20 113135 = 57340 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_113135 : ∀ j : Fin 20,
    113135 ≤ acceleratedOrbit j.val 113135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_113135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 113135) = 531441 * m + 57340 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 113135
  rw [data_20_113135.1, data_20_113135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_113135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 113135) < 1048576 * m + 113135 := by
  apply descent_of_endpoint
  · rw [data_20_113135.1]; exact data_20_113135.2.2
  · rw [data_20_113135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 113279). -/
theorem data_20_113279 : oddCount 113279 20 = 12 ∧
    acceleratedOrbit 20 113279 = 57413 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_113279 : ∀ j : Fin 20,
    113279 ≤ acceleratedOrbit j.val 113279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_113279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 113279) = 531441 * m + 57413 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 113279
  rw [data_20_113279.1, data_20_113279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_113279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 113279) < 1048576 * m + 113279 := by
  apply descent_of_endpoint
  · rw [data_20_113279.1]; exact data_20_113279.2.2
  · rw [data_20_113279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 114075). -/
theorem data_20_114075 : oddCount 114075 20 = 12 ∧
    acceleratedOrbit 20 114075 = 57817 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_114075 : ∀ j : Fin 20,
    114075 ≤ acceleratedOrbit j.val 114075 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_114075 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 114075) = 531441 * m + 57817 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 114075
  rw [data_20_114075.1, data_20_114075.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_114075 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 114075) < 1048576 * m + 114075 := by
  apply descent_of_endpoint
  · rw [data_20_114075.1]; exact data_20_114075.2.2
  · rw [data_20_114075.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 114279). -/
theorem data_20_114279 : oddCount 114279 20 = 12 ∧
    acceleratedOrbit 20 114279 = 57920 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_114279 : ∀ j : Fin 20,
    114279 ≤ acceleratedOrbit j.val 114279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_114279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 114279) = 531441 * m + 57920 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 114279
  rw [data_20_114279.1, data_20_114279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_114279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 114279) < 1048576 * m + 114279 := by
  apply descent_of_endpoint
  · rw [data_20_114279.1]; exact data_20_114279.2.2
  · rw [data_20_114279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 114715). -/
theorem data_20_114715 : oddCount 114715 20 = 12 ∧
    acceleratedOrbit 20 114715 = 58141 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_114715 : ∀ j : Fin 20,
    114715 ≤ acceleratedOrbit j.val 114715 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_114715 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 114715) = 531441 * m + 58141 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 114715
  rw [data_20_114715.1, data_20_114715.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_114715 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 114715) < 1048576 * m + 114715 := by
  apply descent_of_endpoint
  · rw [data_20_114715.1]; exact data_20_114715.2.2
  · rw [data_20_114715.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 115291). -/
theorem data_20_115291 : oddCount 115291 20 = 12 ∧
    acceleratedOrbit 20 115291 = 58433 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_115291 : ∀ j : Fin 20,
    115291 ≤ acceleratedOrbit j.val 115291 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_115291 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 115291) = 531441 * m + 58433 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 115291
  rw [data_20_115291.1, data_20_115291.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_115291 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 115291) < 1048576 * m + 115291 := by
  apply descent_of_endpoint
  · rw [data_20_115291.1]; exact data_20_115291.2.2
  · rw [data_20_115291.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 115647). -/
theorem data_20_115647 : oddCount 115647 20 = 12 ∧
    acceleratedOrbit 20 115647 = 58613 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_115647 : ∀ j : Fin 20,
    115647 ≤ acceleratedOrbit j.val 115647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_115647 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 115647) = 531441 * m + 58613 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 115647
  rw [data_20_115647.1, data_20_115647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_115647 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 115647) < 1048576 * m + 115647 := by
  apply descent_of_endpoint
  · rw [data_20_115647.1]; exact data_20_115647.2.2
  · rw [data_20_115647.2.1]; decide

end Collatz.Research.FirstDescent.Batch259
