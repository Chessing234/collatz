import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 21. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch021
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 3163). -/
theorem data_15_3163 : oddCount 3163 15 = 9 ∧
    acceleratedOrbit 15 3163 = 1901 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_3163 : ∀ j : Fin 15,
    3163 ≤ acceleratedOrbit j.val 3163 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_3163 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3163) = 19683 * m + 1901 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 3163
  rw [data_15_3163.1, data_15_3163.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_3163 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3163) < 32768 * m + 3163 := by
  apply descent_of_endpoint
  · rw [data_15_3163.1]; exact data_15_3163.2.2
  · rw [data_15_3163.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 3303). -/
theorem data_15_3303 : oddCount 3303 15 = 9 ∧
    acceleratedOrbit 15 3303 = 1985 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_3303 : ∀ j : Fin 15,
    3303 ≤ acceleratedOrbit j.val 3303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_3303 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3303) = 19683 * m + 1985 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 3303
  rw [data_15_3303.1, data_15_3303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_3303 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3303) < 32768 * m + 3303 := by
  apply descent_of_endpoint
  · rw [data_15_3303.1]; exact data_15_3303.2.2
  · rw [data_15_3303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 3611). -/
theorem data_15_3611 : oddCount 3611 15 = 9 ∧
    acceleratedOrbit 15 3611 = 2170 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_3611 : ∀ j : Fin 15,
    3611 ≤ acceleratedOrbit j.val 3611 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_3611 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3611) = 19683 * m + 2170 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 3611
  rw [data_15_3611.1, data_15_3611.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_3611 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3611) < 32768 * m + 3611 := by
  apply descent_of_endpoint
  · rw [data_15_3611.1]; exact data_15_3611.2.2
  · rw [data_15_3611.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 3743). -/
theorem data_15_3743 : oddCount 3743 15 = 9 ∧
    acceleratedOrbit 15 3743 = 2249 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_3743 : ∀ j : Fin 15,
    3743 ≤ acceleratedOrbit j.val 3743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_3743 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3743) = 19683 * m + 2249 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 3743
  rw [data_15_3743.1, data_15_3743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_3743 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 3743) < 32768 * m + 3743 := by
  apply descent_of_endpoint
  · rw [data_15_3743.1]; exact data_15_3743.2.2
  · rw [data_15_3743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 4007). -/
theorem data_15_4007 : oddCount 4007 15 = 9 ∧
    acceleratedOrbit 15 4007 = 2408 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_4007 : ∀ j : Fin 15,
    4007 ≤ acceleratedOrbit j.val 4007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_4007 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4007) = 19683 * m + 2408 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 4007
  rw [data_15_4007.1, data_15_4007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_4007 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4007) < 32768 * m + 4007 := by
  apply descent_of_endpoint
  · rw [data_15_4007.1]; exact data_15_4007.2.2
  · rw [data_15_4007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 4031). -/
theorem data_15_4031 : oddCount 4031 15 = 9 ∧
    acceleratedOrbit 15 4031 = 2422 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_4031 : ∀ j : Fin 15,
    4031 ≤ acceleratedOrbit j.val 4031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_4031 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4031) = 19683 * m + 2422 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 4031
  rw [data_15_4031.1, data_15_4031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_4031 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4031) < 32768 * m + 4031 := by
  apply descent_of_endpoint
  · rw [data_15_4031.1]; exact data_15_4031.2.2
  · rw [data_15_4031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 4187). -/
theorem data_15_4187 : oddCount 4187 15 = 9 ∧
    acceleratedOrbit 15 4187 = 2516 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_4187 : ∀ j : Fin 15,
    4187 ≤ acceleratedOrbit j.val 4187 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_4187 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4187) = 19683 * m + 2516 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 4187
  rw [data_15_4187.1, data_15_4187.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_4187 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4187) < 32768 * m + 4187 := by
  apply descent_of_endpoint
  · rw [data_15_4187.1]; exact data_15_4187.2.2
  · rw [data_15_4187.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 4287). -/
theorem data_15_4287 : oddCount 4287 15 = 9 ∧
    acceleratedOrbit 15 4287 = 2576 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_4287 : ∀ j : Fin 15,
    4287 ≤ acceleratedOrbit j.val 4287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_4287 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4287) = 19683 * m + 2576 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 4287
  rw [data_15_4287.1, data_15_4287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_4287 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4287) < 32768 * m + 4287 := by
  apply descent_of_endpoint
  · rw [data_15_4287.1]; exact data_15_4287.2.2
  · rw [data_15_4287.2.1]; decide

end Collatz.Research.FirstDescent.Batch021
