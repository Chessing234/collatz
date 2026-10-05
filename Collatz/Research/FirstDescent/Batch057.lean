import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 57. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch057
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19099). -/
theorem data_16_19099 : oddCount 19099 16 = 10 ∧
    acceleratedOrbit 16 19099 = 17210 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19099 : ∀ j : Fin 16,
    19099 ≤ acceleratedOrbit j.val 19099 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19099 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19099) = 59049 * m + 17210 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19099
  rw [data_16_19099.1, data_16_19099.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19099 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19099) < 65536 * m + 19099 := by
  apply descent_of_endpoint
  · rw [data_16_19099.1]; exact data_16_19099.2.2
  · rw [data_16_19099.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19111). -/
theorem data_16_19111 : oddCount 19111 16 = 10 ∧
    acceleratedOrbit 16 19111 = 17221 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19111 : ∀ j : Fin 16,
    19111 ≤ acceleratedOrbit j.val 19111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19111 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19111) = 59049 * m + 17221 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19111
  rw [data_16_19111.1, data_16_19111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19111 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19111) < 65536 * m + 19111 := by
  apply descent_of_endpoint
  · rw [data_16_19111.1]; exact data_16_19111.2.2
  · rw [data_16_19111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19135). -/
theorem data_16_19135 : oddCount 19135 16 = 10 ∧
    acceleratedOrbit 16 19135 = 17242 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19135 : ∀ j : Fin 16,
    19135 ≤ acceleratedOrbit j.val 19135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19135) = 59049 * m + 17242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19135
  rw [data_16_19135.1, data_16_19135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19135) < 65536 * m + 19135 := by
  apply descent_of_endpoint
  · rw [data_16_19135.1]; exact data_16_19135.2.2
  · rw [data_16_19135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19151). -/
theorem data_16_19151 : oddCount 19151 16 = 10 ∧
    acceleratedOrbit 16 19151 = 17257 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19151 : ∀ j : Fin 16,
    19151 ≤ acceleratedOrbit j.val 19151 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19151 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19151) = 59049 * m + 17257 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19151
  rw [data_16_19151.1, data_16_19151.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19151 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19151) < 65536 * m + 19151 := by
  apply descent_of_endpoint
  · rw [data_16_19151.1]; exact data_16_19151.2.2
  · rw [data_16_19151.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19231). -/
theorem data_16_19231 : oddCount 19231 16 = 10 ∧
    acceleratedOrbit 16 19231 = 17329 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19231 : ∀ j : Fin 16,
    19231 ≤ acceleratedOrbit j.val 19231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19231) = 59049 * m + 17329 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19231
  rw [data_16_19231.1, data_16_19231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19231) < 65536 * m + 19231 := by
  apply descent_of_endpoint
  · rw [data_16_19231.1]; exact data_16_19231.2.2
  · rw [data_16_19231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19367). -/
theorem data_16_19367 : oddCount 19367 16 = 10 ∧
    acceleratedOrbit 16 19367 = 17452 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19367 : ∀ j : Fin 16,
    19367 ≤ acceleratedOrbit j.val 19367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19367 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19367) = 59049 * m + 17452 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19367
  rw [data_16_19367.1, data_16_19367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19367 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19367) < 65536 * m + 19367 := by
  apply descent_of_endpoint
  · rw [data_16_19367.1]; exact data_16_19367.2.2
  · rw [data_16_19367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19547). -/
theorem data_16_19547 : oddCount 19547 16 = 10 ∧
    acceleratedOrbit 16 19547 = 17614 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19547 : ∀ j : Fin 16,
    19547 ≤ acceleratedOrbit j.val 19547 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19547 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19547) = 59049 * m + 17614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19547
  rw [data_16_19547.1, data_16_19547.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19547 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19547) < 65536 * m + 19547 := by
  apply descent_of_endpoint
  · rw [data_16_19547.1]; exact data_16_19547.2.2
  · rw [data_16_19547.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 19687). -/
theorem data_16_19687 : oddCount 19687 16 = 10 ∧
    acceleratedOrbit 16 19687 = 17740 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_19687 : ∀ j : Fin 16,
    19687 ≤ acceleratedOrbit j.val 19687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_19687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19687) = 59049 * m + 17740 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 19687
  rw [data_16_19687.1, data_16_19687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_19687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 19687) < 65536 * m + 19687 := by
  apply descent_of_endpoint
  · rw [data_16_19687.1]; exact data_16_19687.2.2
  · rw [data_16_19687.2.1]; decide

end Collatz.Research.FirstDescent.Batch057
