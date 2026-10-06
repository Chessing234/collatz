import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 221. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch221
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 2511). -/
theorem data_20_2511 : oddCount 2511 20 = 12 ∧
    acceleratedOrbit 20 2511 = 1274 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_2511 : ∀ j : Fin 20,
    2511 ≤ acceleratedOrbit j.val 2511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_2511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2511) = 531441 * m + 1274 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 2511
  rw [data_20_2511.1, data_20_2511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_2511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2511) < 1048576 * m + 2511 := by
  apply descent_of_endpoint
  · rw [data_20_2511.1]; exact data_20_2511.2.2
  · rw [data_20_2511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 2879). -/
theorem data_20_2879 : oddCount 2879 20 = 12 ∧
    acceleratedOrbit 20 2879 = 1460 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_2879 : ∀ j : Fin 20,
    2879 ≤ acceleratedOrbit j.val 2879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_2879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2879) = 531441 * m + 1460 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 2879
  rw [data_20_2879.1, data_20_2879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_2879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 2879) < 1048576 * m + 2879 := by
  apply descent_of_endpoint
  · rw [data_20_2879.1]; exact data_20_2879.2.2
  · rw [data_20_2879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 3199). -/
theorem data_20_3199 : oddCount 3199 20 = 12 ∧
    acceleratedOrbit 20 3199 = 1622 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_3199 : ∀ j : Fin 20,
    3199 ≤ acceleratedOrbit j.val 3199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_3199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 3199) = 531441 * m + 1622 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 3199
  rw [data_20_3199.1, data_20_3199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_3199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 3199) < 1048576 * m + 3199 := by
  apply descent_of_endpoint
  · rw [data_20_3199.1]; exact data_20_3199.2.2
  · rw [data_20_3199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 3279). -/
theorem data_20_3279 : oddCount 3279 20 = 12 ∧
    acceleratedOrbit 20 3279 = 1663 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_3279 : ∀ j : Fin 20,
    3279 ≤ acceleratedOrbit j.val 3279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_3279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 3279) = 531441 * m + 1663 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 3279
  rw [data_20_3279.1, data_20_3279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_3279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 3279) < 1048576 * m + 3279 := by
  apply descent_of_endpoint
  · rw [data_20_3279.1]; exact data_20_3279.2.2
  · rw [data_20_3279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 3871). -/
theorem data_20_3871 : oddCount 3871 20 = 12 ∧
    acceleratedOrbit 20 3871 = 1963 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_3871 : ∀ j : Fin 20,
    3871 ≤ acceleratedOrbit j.val 3871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_3871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 3871) = 531441 * m + 1963 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 3871
  rw [data_20_3871.1, data_20_3871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_3871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 3871) < 1048576 * m + 3871 := by
  apply descent_of_endpoint
  · rw [data_20_3871.1]; exact data_20_3871.2.2
  · rw [data_20_3871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 4167). -/
theorem data_20_4167 : oddCount 4167 20 = 12 ∧
    acceleratedOrbit 20 4167 = 2113 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_4167 : ∀ j : Fin 20,
    4167 ≤ acceleratedOrbit j.val 4167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_4167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 4167) = 531441 * m + 2113 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 4167
  rw [data_20_4167.1, data_20_4167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_4167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 4167) < 1048576 * m + 4167 := by
  apply descent_of_endpoint
  · rw [data_20_4167.1]; exact data_20_4167.2.2
  · rw [data_20_4167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 4351). -/
theorem data_20_4351 : oddCount 4351 20 = 12 ∧
    acceleratedOrbit 20 4351 = 2206 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_4351 : ∀ j : Fin 20,
    4351 ≤ acceleratedOrbit j.val 4351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_4351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 4351) = 531441 * m + 2206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 4351
  rw [data_20_4351.1, data_20_4351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_4351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 4351) < 1048576 * m + 4351 := by
  apply descent_of_endpoint
  · rw [data_20_4351.1]; exact data_20_4351.2.2
  · rw [data_20_4351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 4511). -/
theorem data_20_4511 : oddCount 4511 20 = 12 ∧
    acceleratedOrbit 20 4511 = 2287 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_4511 : ∀ j : Fin 20,
    4511 ≤ acceleratedOrbit j.val 4511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_4511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 4511) = 531441 * m + 2287 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 4511
  rw [data_20_4511.1, data_20_4511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_4511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 4511) < 1048576 * m + 4511 := by
  apply descent_of_endpoint
  · rw [data_20_4511.1]; exact data_20_4511.2.2
  · rw [data_20_4511.2.1]; decide

end Collatz.Research.FirstDescent.Batch221
