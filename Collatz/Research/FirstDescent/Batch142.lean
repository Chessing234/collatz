import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 142. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch142
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 88959). -/
theorem data_18_88959 : oddCount 88959 18 = 11 ∧
    acceleratedOrbit 18 88959 = 60116 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_88959 : ∀ j : Fin 18,
    88959 ≤ acceleratedOrbit j.val 88959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_88959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 88959) = 177147 * m + 60116 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 88959
  rw [data_18_88959.1, data_18_88959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_88959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 88959) < 262144 * m + 88959 := by
  apply descent_of_endpoint
  · rw [data_18_88959.1]; exact data_18_88959.2.2
  · rw [data_18_88959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 89407). -/
theorem data_18_89407 : oddCount 89407 18 = 11 ∧
    acceleratedOrbit 18 89407 = 60419 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_89407 : ∀ j : Fin 18,
    89407 ≤ acceleratedOrbit j.val 89407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_89407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 89407) = 177147 * m + 60419 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 89407
  rw [data_18_89407.1, data_18_89407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_89407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 89407) < 262144 * m + 89407 := by
  apply descent_of_endpoint
  · rw [data_18_89407.1]; exact data_18_89407.2.2
  · rw [data_18_89407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 90471). -/
theorem data_18_90471 : oddCount 90471 18 = 11 ∧
    acceleratedOrbit 18 90471 = 61138 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_90471 : ∀ j : Fin 18,
    90471 ≤ acceleratedOrbit j.val 90471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_90471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 90471) = 177147 * m + 61138 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 90471
  rw [data_18_90471.1, data_18_90471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_90471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 90471) < 262144 * m + 90471 := by
  apply descent_of_endpoint
  · rw [data_18_90471.1]; exact data_18_90471.2.2
  · rw [data_18_90471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 90591). -/
theorem data_18_90591 : oddCount 90591 18 = 11 ∧
    acceleratedOrbit 18 90591 = 61219 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_90591 : ∀ j : Fin 18,
    90591 ≤ acceleratedOrbit j.val 90591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_90591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 90591) = 177147 * m + 61219 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 90591
  rw [data_18_90591.1, data_18_90591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_90591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 90591) < 262144 * m + 90591 := by
  apply descent_of_endpoint
  · rw [data_18_90591.1]; exact data_18_90591.2.2
  · rw [data_18_90591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 90943). -/
theorem data_18_90943 : oddCount 90943 18 = 11 ∧
    acceleratedOrbit 18 90943 = 61457 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_90943 : ∀ j : Fin 18,
    90943 ≤ acceleratedOrbit j.val 90943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_90943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 90943) = 177147 * m + 61457 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 90943
  rw [data_18_90943.1, data_18_90943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_90943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 90943) < 262144 * m + 90943 := by
  apply descent_of_endpoint
  · rw [data_18_90943.1]; exact data_18_90943.2.2
  · rw [data_18_90943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 91103). -/
theorem data_18_91103 : oddCount 91103 18 = 11 ∧
    acceleratedOrbit 18 91103 = 61565 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_91103 : ∀ j : Fin 18,
    91103 ≤ acceleratedOrbit j.val 91103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_91103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91103) = 177147 * m + 61565 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 91103
  rw [data_18_91103.1, data_18_91103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_91103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91103) < 262144 * m + 91103 := by
  apply descent_of_endpoint
  · rw [data_18_91103.1]; exact data_18_91103.2.2
  · rw [data_18_91103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 91263). -/
theorem data_18_91263 : oddCount 91263 18 = 11 ∧
    acceleratedOrbit 18 91263 = 61673 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_91263 : ∀ j : Fin 18,
    91263 ≤ acceleratedOrbit j.val 91263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_91263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91263) = 177147 * m + 61673 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 91263
  rw [data_18_91263.1, data_18_91263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_91263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91263) < 262144 * m + 91263 := by
  apply descent_of_endpoint
  · rw [data_18_91263.1]; exact data_18_91263.2.2
  · rw [data_18_91263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 91519). -/
theorem data_18_91519 : oddCount 91519 18 = 11 ∧
    acceleratedOrbit 18 91519 = 61846 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_91519 : ∀ j : Fin 18,
    91519 ≤ acceleratedOrbit j.val 91519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_91519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91519) = 177147 * m + 61846 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 91519
  rw [data_18_91519.1, data_18_91519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_91519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91519) < 262144 * m + 91519 := by
  apply descent_of_endpoint
  · rw [data_18_91519.1]; exact data_18_91519.2.2
  · rw [data_18_91519.2.1]; decide

end Collatz.Research.FirstDescent.Batch142
