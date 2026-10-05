import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 103. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch103
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6399). -/
theorem data_18_6399 : oddCount 6399 18 = 11 ∧
    acceleratedOrbit 18 6399 = 4325 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6399 : ∀ j : Fin 18,
    6399 ≤ acceleratedOrbit j.val 6399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6399 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6399) = 177147 * m + 4325 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6399
  rw [data_18_6399.1, data_18_6399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6399 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6399) < 262144 * m + 6399 := by
  apply descent_of_endpoint
  · rw [data_18_6399.1]; exact data_18_6399.2.2
  · rw [data_18_6399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6527). -/
theorem data_18_6527 : oddCount 6527 18 = 11 ∧
    acceleratedOrbit 18 6527 = 4412 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6527 : ∀ j : Fin 18,
    6527 ≤ acceleratedOrbit j.val 6527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6527) = 177147 * m + 4412 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6527
  rw [data_18_6527.1, data_18_6527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6527) < 262144 * m + 6527 := by
  apply descent_of_endpoint
  · rw [data_18_6527.1]; exact data_18_6527.2.2
  · rw [data_18_6527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6767). -/
theorem data_18_6767 : oddCount 6767 18 = 11 ∧
    acceleratedOrbit 18 6767 = 4574 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6767 : ∀ j : Fin 18,
    6767 ≤ acceleratedOrbit j.val 6767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6767) = 177147 * m + 4574 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6767
  rw [data_18_6767.1, data_18_6767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6767) < 262144 * m + 6767 := by
  apply descent_of_endpoint
  · rw [data_18_6767.1]; exact data_18_6767.2.2
  · rw [data_18_6767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 6847). -/
theorem data_18_6847 : oddCount 6847 18 = 11 ∧
    acceleratedOrbit 18 6847 = 4628 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_6847 : ∀ j : Fin 18,
    6847 ≤ acceleratedOrbit j.val 6847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_6847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6847) = 177147 * m + 4628 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 6847
  rw [data_18_6847.1, data_18_6847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_6847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 6847) < 262144 * m + 6847 := by
  apply descent_of_endpoint
  · rw [data_18_6847.1]; exact data_18_6847.2.2
  · rw [data_18_6847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 7419). -/
theorem data_18_7419 : oddCount 7419 18 = 11 ∧
    acceleratedOrbit 18 7419 = 5015 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_7419 : ∀ j : Fin 18,
    7419 ≤ acceleratedOrbit j.val 7419 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_7419 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 7419) = 177147 * m + 5015 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 7419
  rw [data_18_7419.1, data_18_7419.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_7419 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 7419) < 262144 * m + 7419 := by
  apply descent_of_endpoint
  · rw [data_18_7419.1]; exact data_18_7419.2.2
  · rw [data_18_7419.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 8519). -/
theorem data_18_8519 : oddCount 8519 18 = 11 ∧
    acceleratedOrbit 18 8519 = 5758 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_8519 : ∀ j : Fin 18,
    8519 ≤ acceleratedOrbit j.val 8519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_8519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 8519) = 177147 * m + 5758 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 8519
  rw [data_18_8519.1, data_18_8519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_8519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 8519) < 262144 * m + 8519 := by
  apply descent_of_endpoint
  · rw [data_18_8519.1]; exact data_18_8519.2.2
  · rw [data_18_8519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 8603). -/
theorem data_18_8603 : oddCount 8603 18 = 11 ∧
    acceleratedOrbit 18 8603 = 5815 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_8603 : ∀ j : Fin 18,
    8603 ≤ acceleratedOrbit j.val 8603 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_8603 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 8603) = 177147 * m + 5815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 8603
  rw [data_18_8603.1, data_18_8603.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_8603 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 8603) < 262144 * m + 8603 := by
  apply descent_of_endpoint
  · rw [data_18_8603.1]; exact data_18_8603.2.2
  · rw [data_18_8603.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 8955). -/
theorem data_18_8955 : oddCount 8955 18 = 11 ∧
    acceleratedOrbit 18 8955 = 6053 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_8955 : ∀ j : Fin 18,
    8955 ≤ acceleratedOrbit j.val 8955 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_8955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 8955) = 177147 * m + 6053 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 8955
  rw [data_18_8955.1, data_18_8955.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_8955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 8955) < 262144 * m + 8955 := by
  apply descent_of_endpoint
  · rw [data_18_8955.1]; exact data_18_8955.2.2
  · rw [data_18_8955.2.1]; decide

end Collatz.Research.FirstDescent.Batch103
