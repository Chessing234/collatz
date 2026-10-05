import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 18. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch018
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7911). -/
theorem data_13_7911 : oddCount 7911 13 = 8 ∧
    acceleratedOrbit 13 7911 = 6337 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7911 : ∀ j : Fin 13,
    7911 ≤ acceleratedOrbit j.val 7911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7911 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7911) = 6561 * m + 6337 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7911
  rw [data_13_7911.1, data_13_7911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7911 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7911) < 8192 * m + 7911 := by
  apply descent_of_endpoint
  · rw [data_13_7911.1]; exact data_13_7911.2.2
  · rw [data_13_7911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 7967). -/
theorem data_13_7967 : oddCount 7967 13 = 8 ∧
    acceleratedOrbit 13 7967 = 6382 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_7967 : ∀ j : Fin 13,
    7967 ≤ acceleratedOrbit j.val 7967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_7967 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7967) = 6561 * m + 6382 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 7967
  rw [data_13_7967.1, data_13_7967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_7967 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 7967) < 8192 * m + 7967 := by
  apply descent_of_endpoint
  · rw [data_13_7967.1]; exact data_13_7967.2.2
  · rw [data_13_7967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 8047). -/
theorem data_13_8047 : oddCount 8047 13 = 8 ∧
    acceleratedOrbit 13 8047 = 6446 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_8047 : ∀ j : Fin 13,
    8047 ≤ acceleratedOrbit j.val 8047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_8047 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 8047) = 6561 * m + 6446 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 8047
  rw [data_13_8047.1, data_13_8047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_8047 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 8047) < 8192 * m + 8047 := by
  apply descent_of_endpoint
  · rw [data_13_8047.1]; exact data_13_8047.2.2
  · rw [data_13_8047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 8103). -/
theorem data_13_8103 : oddCount 8103 13 = 8 ∧
    acceleratedOrbit 13 8103 = 6491 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_8103 : ∀ j : Fin 13,
    8103 ≤ acceleratedOrbit j.val 8103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_8103 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 8103) = 6561 * m + 6491 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 8103
  rw [data_13_8103.1, data_13_8103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_8103 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 8103) < 8192 * m + 8103 := by
  apply descent_of_endpoint
  · rw [data_13_8103.1]; exact data_13_8103.2.2
  · rw [data_13_8103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 127). -/
theorem data_15_127 : oddCount 127 15 = 9 ∧
    acceleratedOrbit 15 127 = 77 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_127 : ∀ j : Fin 15,
    127 ≤ acceleratedOrbit j.val 127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_127 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 127) = 19683 * m + 77 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 127
  rw [data_15_127.1, data_15_127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_127 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 127) < 32768 * m + 127 := by
  apply descent_of_endpoint
  · rw [data_15_127.1]; exact data_15_127.2.2
  · rw [data_15_127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 411). -/
theorem data_15_411 : oddCount 411 15 = 9 ∧
    acceleratedOrbit 15 411 = 248 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_411 : ∀ j : Fin 15,
    411 ≤ acceleratedOrbit j.val 411 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_411 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 411) = 19683 * m + 248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 411
  rw [data_15_411.1, data_15_411.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_411 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 411) < 32768 * m + 411 := by
  apply descent_of_endpoint
  · rw [data_15_411.1]; exact data_15_411.2.2
  · rw [data_15_411.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 415). -/
theorem data_15_415 : oddCount 415 15 = 9 ∧
    acceleratedOrbit 15 415 = 250 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_415 : ∀ j : Fin 15,
    415 ≤ acceleratedOrbit j.val 415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_415 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 415) = 19683 * m + 250 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 415
  rw [data_15_415.1, data_15_415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_415 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 415) < 32768 * m + 415 := by
  apply descent_of_endpoint
  · rw [data_15_415.1]; exact data_15_415.2.2
  · rw [data_15_415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 831). -/
theorem data_15_831 : oddCount 831 15 = 9 ∧
    acceleratedOrbit 15 831 = 500 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_831 : ∀ j : Fin 15,
    831 ≤ acceleratedOrbit j.val 831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_831 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 831) = 19683 * m + 500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 831
  rw [data_15_831.1, data_15_831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_831 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 831) < 32768 * m + 831 := by
  apply descent_of_endpoint
  · rw [data_15_831.1]; exact data_15_831.2.2
  · rw [data_15_831.2.1]; decide

end Collatz.Research.FirstDescent.Batch018
