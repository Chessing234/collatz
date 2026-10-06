import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 4. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch004
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (10, 999). -/
theorem data_10_999 : oddCount 999 10 = 6 ∧
    acceleratedOrbit 10 999 = 712 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_999 : ∀ j : Fin 10,
    999 ≤ acceleratedOrbit j.val 999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_999 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 999) = 729 * m + 712 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 999
  rw [data_10_999.1, data_10_999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_999 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 999) < 1024 * m + 999 := by
  apply descent_of_endpoint
  · rw [data_10_999.1]; exact data_10_999.2.2
  · rw [data_10_999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 231). -/
theorem data_12_231 : oddCount 231 12 = 7 ∧
    acceleratedOrbit 12 231 = 124 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_231 : ∀ j : Fin 12,
    231 ≤ acceleratedOrbit j.val 231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_231 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 231) = 2187 * m + 124 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 231
  rw [data_12_231.1, data_12_231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_231 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 231) < 4096 * m + 231 := by
  apply descent_of_endpoint
  · rw [data_12_231.1]; exact data_12_231.2.2
  · rw [data_12_231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 383). -/
theorem data_12_383 : oddCount 383 12 = 7 ∧
    acceleratedOrbit 12 383 = 205 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_383 : ∀ j : Fin 12,
    383 ≤ acceleratedOrbit j.val 383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_383 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 383) = 2187 * m + 205 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 383
  rw [data_12_383.1, data_12_383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_383 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 383) < 4096 * m + 383 := by
  apply descent_of_endpoint
  · rw [data_12_383.1]; exact data_12_383.2.2
  · rw [data_12_383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 463). -/
theorem data_12_463 : oddCount 463 12 = 7 ∧
    acceleratedOrbit 12 463 = 248 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_463 : ∀ j : Fin 12,
    463 ≤ acceleratedOrbit j.val 463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_463 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 463) = 2187 * m + 248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 463
  rw [data_12_463.1, data_12_463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_463 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 463) < 4096 * m + 463 := by
  apply descent_of_endpoint
  · rw [data_12_463.1]; exact data_12_463.2.2
  · rw [data_12_463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 615). -/
theorem data_12_615 : oddCount 615 12 = 7 ∧
    acceleratedOrbit 12 615 = 329 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_615 : ∀ j : Fin 12,
    615 ≤ acceleratedOrbit j.val 615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_615 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 615) = 2187 * m + 329 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 615
  rw [data_12_615.1, data_12_615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_615 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 615) < 4096 * m + 615 := by
  apply descent_of_endpoint
  · rw [data_12_615.1]; exact data_12_615.2.2
  · rw [data_12_615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 879). -/
theorem data_12_879 : oddCount 879 12 = 7 ∧
    acceleratedOrbit 12 879 = 470 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_879 : ∀ j : Fin 12,
    879 ≤ acceleratedOrbit j.val 879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_879 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 879) = 2187 * m + 470 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 879
  rw [data_12_879.1, data_12_879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_879 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 879) < 4096 * m + 879 := by
  apply descent_of_endpoint
  · rw [data_12_879.1]; exact data_12_879.2.2
  · rw [data_12_879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 935). -/
theorem data_12_935 : oddCount 935 12 = 7 ∧
    acceleratedOrbit 12 935 = 500 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_935 : ∀ j : Fin 12,
    935 ≤ acceleratedOrbit j.val 935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_935 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 935) = 2187 * m + 500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 935
  rw [data_12_935.1, data_12_935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_935 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 935) < 4096 * m + 935 := by
  apply descent_of_endpoint
  · rw [data_12_935.1]; exact data_12_935.2.2
  · rw [data_12_935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1019). -/
theorem data_12_1019 : oddCount 1019 12 = 7 ∧
    acceleratedOrbit 12 1019 = 545 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1019 : ∀ j : Fin 12,
    1019 ≤ acceleratedOrbit j.val 1019 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1019 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1019) = 2187 * m + 545 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1019
  rw [data_12_1019.1, data_12_1019.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1019 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1019) < 4096 * m + 1019 := by
  apply descent_of_endpoint
  · rw [data_12_1019.1]; exact data_12_1019.2.2
  · rw [data_12_1019.2.1]; decide

end Collatz.Research.FirstDescent.Batch004
