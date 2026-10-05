import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 210. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch210
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 239975). -/
theorem data_18_239975 : oddCount 239975 18 = 11 ∧
    acceleratedOrbit 18 239975 = 162167 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_239975 : ∀ j : Fin 18,
    239975 ≤ acceleratedOrbit j.val 239975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_239975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 239975) = 177147 * m + 162167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 239975
  rw [data_18_239975.1, data_18_239975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_239975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 239975) < 262144 * m + 239975 := by
  apply descent_of_endpoint
  · rw [data_18_239975.1]; exact data_18_239975.2.2
  · rw [data_18_239975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 240103). -/
theorem data_18_240103 : oddCount 240103 18 = 11 ∧
    acceleratedOrbit 18 240103 = 162254 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_240103 : ∀ j : Fin 18,
    240103 ≤ acceleratedOrbit j.val 240103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_240103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240103) = 177147 * m + 162254 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 240103
  rw [data_18_240103.1, data_18_240103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_240103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240103) < 262144 * m + 240103 := by
  apply descent_of_endpoint
  · rw [data_18_240103.1]; exact data_18_240103.2.2
  · rw [data_18_240103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 240255). -/
theorem data_18_240255 : oddCount 240255 18 = 11 ∧
    acceleratedOrbit 18 240255 = 162356 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_240255 : ∀ j : Fin 18,
    240255 ≤ acceleratedOrbit j.val 240255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_240255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240255) = 177147 * m + 162356 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 240255
  rw [data_18_240255.1, data_18_240255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_240255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240255) < 262144 * m + 240255 := by
  apply descent_of_endpoint
  · rw [data_18_240255.1]; exact data_18_240255.2.2
  · rw [data_18_240255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 240511). -/
theorem data_18_240511 : oddCount 240511 18 = 11 ∧
    acceleratedOrbit 18 240511 = 162529 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_240511 : ∀ j : Fin 18,
    240511 ≤ acceleratedOrbit j.val 240511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_240511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240511) = 177147 * m + 162529 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 240511
  rw [data_18_240511.1, data_18_240511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_240511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240511) < 262144 * m + 240511 := by
  apply descent_of_endpoint
  · rw [data_18_240511.1]; exact data_18_240511.2.2
  · rw [data_18_240511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 240623). -/
theorem data_18_240623 : oddCount 240623 18 = 11 ∧
    acceleratedOrbit 18 240623 = 162605 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_240623 : ∀ j : Fin 18,
    240623 ≤ acceleratedOrbit j.val 240623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_240623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240623) = 177147 * m + 162605 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 240623
  rw [data_18_240623.1, data_18_240623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_240623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 240623) < 262144 * m + 240623 := by
  apply descent_of_endpoint
  · rw [data_18_240623.1]; exact data_18_240623.2.2
  · rw [data_18_240623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 242559). -/
theorem data_18_242559 : oddCount 242559 18 = 11 ∧
    acceleratedOrbit 18 242559 = 163913 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_242559 : ∀ j : Fin 18,
    242559 ≤ acceleratedOrbit j.val 242559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_242559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 242559) = 177147 * m + 163913 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 242559
  rw [data_18_242559.1, data_18_242559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_242559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 242559) < 262144 * m + 242559 := by
  apply descent_of_endpoint
  · rw [data_18_242559.1]; exact data_18_242559.2.2
  · rw [data_18_242559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 242815). -/
theorem data_18_242815 : oddCount 242815 18 = 11 ∧
    acceleratedOrbit 18 242815 = 164086 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_242815 : ∀ j : Fin 18,
    242815 ≤ acceleratedOrbit j.val 242815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_242815 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 242815) = 177147 * m + 164086 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 242815
  rw [data_18_242815.1, data_18_242815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_242815 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 242815) < 262144 * m + 242815 := by
  apply descent_of_endpoint
  · rw [data_18_242815.1]; exact data_18_242815.2.2
  · rw [data_18_242815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 243047). -/
theorem data_18_243047 : oddCount 243047 18 = 11 ∧
    acceleratedOrbit 18 243047 = 164243 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_243047 : ∀ j : Fin 18,
    243047 ≤ acceleratedOrbit j.val 243047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_243047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 243047) = 177147 * m + 164243 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 243047
  rw [data_18_243047.1, data_18_243047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_243047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 243047) < 262144 * m + 243047 := by
  apply descent_of_endpoint
  · rw [data_18_243047.1]; exact data_18_243047.2.2
  · rw [data_18_243047.2.1]; decide

end Collatz.Research.FirstDescent.Batch210
