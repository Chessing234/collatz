import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 53. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch053
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15103). -/
theorem data_16_15103 : oddCount 15103 16 = 10 ∧
    acceleratedOrbit 16 15103 = 13609 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15103 : ∀ j : Fin 16,
    15103 ≤ acceleratedOrbit j.val 15103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15103) = 59049 * m + 13609 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15103
  rw [data_16_15103.1, data_16_15103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15103) < 65536 * m + 15103 := by
  apply descent_of_endpoint
  · rw [data_16_15103.1]; exact data_16_15103.2.2
  · rw [data_16_15103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15167). -/
theorem data_16_15167 : oddCount 15167 16 = 10 ∧
    acceleratedOrbit 16 15167 = 13667 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15167 : ∀ j : Fin 16,
    15167 ≤ acceleratedOrbit j.val 15167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15167) = 59049 * m + 13667 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15167
  rw [data_16_15167.1, data_16_15167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15167) < 65536 * m + 15167 := by
  apply descent_of_endpoint
  · rw [data_16_15167.1]; exact data_16_15167.2.2
  · rw [data_16_15167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15207). -/
theorem data_16_15207 : oddCount 15207 16 = 10 ∧
    acceleratedOrbit 16 15207 = 13703 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15207 : ∀ j : Fin 16,
    15207 ≤ acceleratedOrbit j.val 15207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15207) = 59049 * m + 13703 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15207
  rw [data_16_15207.1, data_16_15207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15207) < 65536 * m + 15207 := by
  apply descent_of_endpoint
  · rw [data_16_15207.1]; exact data_16_15207.2.2
  · rw [data_16_15207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15423). -/
theorem data_16_15423 : oddCount 15423 16 = 10 ∧
    acceleratedOrbit 16 15423 = 13898 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15423 : ∀ j : Fin 16,
    15423 ≤ acceleratedOrbit j.val 15423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15423) = 59049 * m + 13898 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15423
  rw [data_16_15423.1, data_16_15423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15423) < 65536 * m + 15423 := by
  apply descent_of_endpoint
  · rw [data_16_15423.1]; exact data_16_15423.2.2
  · rw [data_16_15423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15487). -/
theorem data_16_15487 : oddCount 15487 16 = 10 ∧
    acceleratedOrbit 16 15487 = 13955 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15487 : ∀ j : Fin 16,
    15487 ≤ acceleratedOrbit j.val 15487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15487) = 59049 * m + 13955 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15487
  rw [data_16_15487.1, data_16_15487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15487) < 65536 * m + 15487 := by
  apply descent_of_endpoint
  · rw [data_16_15487.1]; exact data_16_15487.2.2
  · rw [data_16_15487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15515). -/
theorem data_16_15515 : oddCount 15515 16 = 10 ∧
    acceleratedOrbit 16 15515 = 13981 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15515 : ∀ j : Fin 16,
    15515 ≤ acceleratedOrbit j.val 15515 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15515 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15515) = 59049 * m + 13981 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15515
  rw [data_16_15515.1, data_16_15515.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15515 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15515) < 65536 * m + 15515 := by
  apply descent_of_endpoint
  · rw [data_16_15515.1]; exact data_16_15515.2.2
  · rw [data_16_15515.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15599). -/
theorem data_16_15599 : oddCount 15599 16 = 10 ∧
    acceleratedOrbit 16 15599 = 14056 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15599 : ∀ j : Fin 16,
    15599 ≤ acceleratedOrbit j.val 15599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15599) = 59049 * m + 14056 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15599
  rw [data_16_15599.1, data_16_15599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15599) < 65536 * m + 15599 := by
  apply descent_of_endpoint
  · rw [data_16_15599.1]; exact data_16_15599.2.2
  · rw [data_16_15599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 15643). -/
theorem data_16_15643 : oddCount 15643 16 = 10 ∧
    acceleratedOrbit 16 15643 = 14096 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_15643 : ∀ j : Fin 16,
    15643 ≤ acceleratedOrbit j.val 15643 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_15643 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15643) = 59049 * m + 14096 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 15643
  rw [data_16_15643.1, data_16_15643.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_15643 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 15643) < 65536 * m + 15643 := by
  apply descent_of_endpoint
  · rw [data_16_15643.1]; exact data_16_15643.2.2
  · rw [data_16_15643.2.1]; decide

end Collatz.Research.FirstDescent.Batch053
