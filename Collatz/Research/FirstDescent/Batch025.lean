import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 25. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch025
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 9679). -/
theorem data_15_9679 : oddCount 9679 15 = 9 ∧
    acceleratedOrbit 15 9679 = 5815 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_9679 : ∀ j : Fin 15,
    9679 ≤ acceleratedOrbit j.val 9679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_9679 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9679) = 19683 * m + 5815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 9679
  rw [data_15_9679.1, data_15_9679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_9679 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9679) < 32768 * m + 9679 := by
  apply descent_of_endpoint
  · rw [data_15_9679.1]; exact data_15_9679.2.2
  · rw [data_15_9679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 9711). -/
theorem data_15_9711 : oddCount 9711 15 = 9 ∧
    acceleratedOrbit 15 9711 = 5834 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_9711 : ∀ j : Fin 15,
    9711 ≤ acceleratedOrbit j.val 9711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_9711 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9711) = 19683 * m + 5834 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 9711
  rw [data_15_9711.1, data_15_9711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_9711 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9711) < 32768 * m + 9711 := by
  apply descent_of_endpoint
  · rw [data_15_9711.1]; exact data_15_9711.2.2
  · rw [data_15_9711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 9959). -/
theorem data_15_9959 : oddCount 9959 15 = 9 ∧
    acceleratedOrbit 15 9959 = 5983 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_9959 : ∀ j : Fin 15,
    9959 ≤ acceleratedOrbit j.val 9959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_9959 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9959) = 19683 * m + 5983 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 9959
  rw [data_15_9959.1, data_15_9959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_9959 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 9959) < 32768 * m + 9959 := by
  apply descent_of_endpoint
  · rw [data_15_9959.1]; exact data_15_9959.2.2
  · rw [data_15_9959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 10055). -/
theorem data_15_10055 : oddCount 10055 15 = 9 ∧
    acceleratedOrbit 15 10055 = 6041 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_10055 : ∀ j : Fin 15,
    10055 ≤ acceleratedOrbit j.val 10055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_10055 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10055) = 19683 * m + 6041 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 10055
  rw [data_15_10055.1, data_15_10055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_10055 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10055) < 32768 * m + 10055 := by
  apply descent_of_endpoint
  · rw [data_15_10055.1]; exact data_15_10055.2.2
  · rw [data_15_10055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 10075). -/
theorem data_15_10075 : oddCount 10075 15 = 9 ∧
    acceleratedOrbit 15 10075 = 6053 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_10075 : ∀ j : Fin 15,
    10075 ≤ acceleratedOrbit j.val 10075 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_10075 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10075) = 19683 * m + 6053 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 10075
  rw [data_15_10075.1, data_15_10075.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_10075 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10075) < 32768 * m + 10075 := by
  apply descent_of_endpoint
  · rw [data_15_10075.1]; exact data_15_10075.2.2
  · rw [data_15_10075.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 10655). -/
theorem data_15_10655 : oddCount 10655 15 = 9 ∧
    acceleratedOrbit 15 10655 = 6401 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_10655 : ∀ j : Fin 15,
    10655 ≤ acceleratedOrbit j.val 10655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_10655 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10655) = 19683 * m + 6401 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 10655
  rw [data_15_10655.1, data_15_10655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_10655 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10655) < 32768 * m + 10655 := by
  apply descent_of_endpoint
  · rw [data_15_10655.1]; exact data_15_10655.2.2
  · rw [data_15_10655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 10735). -/
theorem data_15_10735 : oddCount 10735 15 = 9 ∧
    acceleratedOrbit 15 10735 = 6449 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_10735 : ∀ j : Fin 15,
    10735 ≤ acceleratedOrbit j.val 10735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_10735 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10735) = 19683 * m + 6449 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 10735
  rw [data_15_10735.1, data_15_10735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_10735 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10735) < 32768 * m + 10735 := by
  apply descent_of_endpoint
  · rw [data_15_10735.1]; exact data_15_10735.2.2
  · rw [data_15_10735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 10863). -/
theorem data_15_10863 : oddCount 10863 15 = 9 ∧
    acceleratedOrbit 15 10863 = 6526 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_10863 : ∀ j : Fin 15,
    10863 ≤ acceleratedOrbit j.val 10863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_10863 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10863) = 19683 * m + 6526 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 10863
  rw [data_15_10863.1, data_15_10863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_10863 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 10863) < 32768 * m + 10863 := by
  apply descent_of_endpoint
  · rw [data_15_10863.1]; exact data_15_10863.2.2
  · rw [data_15_10863.2.1]; decide

end Collatz.Research.FirstDescent.Batch025
