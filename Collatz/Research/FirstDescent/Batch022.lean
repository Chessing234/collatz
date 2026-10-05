import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 22. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch022
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 4655). -/
theorem data_15_4655 : oddCount 4655 15 = 9 ∧
    acceleratedOrbit 15 4655 = 2797 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_4655 : ∀ j : Fin 15,
    4655 ≤ acceleratedOrbit j.val 4655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_4655 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4655) = 19683 * m + 2797 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 4655
  rw [data_15_4655.1, data_15_4655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_4655 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 4655) < 32768 * m + 4655 := by
  apply descent_of_endpoint
  · rw [data_15_4655.1]; exact data_15_4655.2.2
  · rw [data_15_4655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 5231). -/
theorem data_15_5231 : oddCount 5231 15 = 9 ∧
    acceleratedOrbit 15 5231 = 3143 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_5231 : ∀ j : Fin 15,
    5231 ≤ acceleratedOrbit j.val 5231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_5231 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5231) = 19683 * m + 3143 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 5231
  rw [data_15_5231.1, data_15_5231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_5231 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5231) < 32768 * m + 5231 := by
  apply descent_of_endpoint
  · rw [data_15_5231.1]; exact data_15_5231.2.2
  · rw [data_15_5231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 5311). -/
theorem data_15_5311 : oddCount 5311 15 = 9 ∧
    acceleratedOrbit 15 5311 = 3191 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_5311 : ∀ j : Fin 15,
    5311 ≤ acceleratedOrbit j.val 5311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_5311 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5311) = 19683 * m + 3191 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 5311
  rw [data_15_5311.1, data_15_5311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_5311 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5311) < 32768 * m + 5311 := by
  apply descent_of_endpoint
  · rw [data_15_5311.1]; exact data_15_5311.2.2
  · rw [data_15_5311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 5599). -/
theorem data_15_5599 : oddCount 5599 15 = 9 ∧
    acceleratedOrbit 15 5599 = 3364 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_5599 : ∀ j : Fin 15,
    5599 ≤ acceleratedOrbit j.val 5599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_5599 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5599) = 19683 * m + 3364 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 5599
  rw [data_15_5599.1, data_15_5599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_5599 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5599) < 32768 * m + 5599 := by
  apply descent_of_endpoint
  · rw [data_15_5599.1]; exact data_15_5599.2.2
  · rw [data_15_5599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 5631). -/
theorem data_15_5631 : oddCount 5631 15 = 9 ∧
    acceleratedOrbit 15 5631 = 3383 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_5631 : ∀ j : Fin 15,
    5631 ≤ acceleratedOrbit j.val 5631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_5631 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5631) = 19683 * m + 3383 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 5631
  rw [data_15_5631.1, data_15_5631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_5631 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 5631) < 32768 * m + 5631 := by
  apply descent_of_endpoint
  · rw [data_15_5631.1]; exact data_15_5631.2.2
  · rw [data_15_5631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 6175). -/
theorem data_15_6175 : oddCount 6175 15 = 9 ∧
    acceleratedOrbit 15 6175 = 3710 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_6175 : ∀ j : Fin 15,
    6175 ≤ acceleratedOrbit j.val 6175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_6175 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6175) = 19683 * m + 3710 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 6175
  rw [data_15_6175.1, data_15_6175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_6175 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6175) < 32768 * m + 6175 := by
  apply descent_of_endpoint
  · rw [data_15_6175.1]; exact data_15_6175.2.2
  · rw [data_15_6175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 6255). -/
theorem data_15_6255 : oddCount 6255 15 = 9 ∧
    acceleratedOrbit 15 6255 = 3758 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_6255 : ∀ j : Fin 15,
    6255 ≤ acceleratedOrbit j.val 6255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_6255 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6255) = 19683 * m + 3758 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 6255
  rw [data_15_6255.1, data_15_6255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_6255 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6255) < 32768 * m + 6255 := by
  apply descent_of_endpoint
  · rw [data_15_6255.1]; exact data_15_6255.2.2
  · rw [data_15_6255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 6503). -/
theorem data_15_6503 : oddCount 6503 15 = 9 ∧
    acceleratedOrbit 15 6503 = 3907 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_6503 : ∀ j : Fin 15,
    6503 ≤ acceleratedOrbit j.val 6503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_6503 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6503) = 19683 * m + 3907 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 6503
  rw [data_15_6503.1, data_15_6503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_6503 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 6503) < 32768 * m + 6503 := by
  apply descent_of_endpoint
  · rw [data_15_6503.1]; exact data_15_6503.2.2
  · rw [data_15_6503.2.1]; decide

end Collatz.Research.FirstDescent.Batch022
