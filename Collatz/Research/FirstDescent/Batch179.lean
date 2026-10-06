import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 179. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch179
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169215). -/
theorem data_18_169215 : oddCount 169215 18 = 11 ∧
    acceleratedOrbit 18 169215 = 114350 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169215 : ∀ j : Fin 18,
    169215 ≤ acceleratedOrbit j.val 169215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169215) = 177147 * m + 114350 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169215
  rw [data_18_169215.1, data_18_169215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169215) < 262144 * m + 169215 := by
  apply descent_of_endpoint
  · rw [data_18_169215.1]; exact data_18_169215.2.2
  · rw [data_18_169215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169263). -/
theorem data_18_169263 : oddCount 169263 18 = 11 ∧
    acceleratedOrbit 18 169263 = 114383 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169263 : ∀ j : Fin 18,
    169263 ≤ acceleratedOrbit j.val 169263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169263) = 177147 * m + 114383 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169263
  rw [data_18_169263.1, data_18_169263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169263) < 262144 * m + 169263 := by
  apply descent_of_endpoint
  · rw [data_18_169263.1]; exact data_18_169263.2.2
  · rw [data_18_169263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169423). -/
theorem data_18_169423 : oddCount 169423 18 = 11 ∧
    acceleratedOrbit 18 169423 = 114491 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169423 : ∀ j : Fin 18,
    169423 ≤ acceleratedOrbit j.val 169423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169423) = 177147 * m + 114491 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169423
  rw [data_18_169423.1, data_18_169423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169423) < 262144 * m + 169423 := by
  apply descent_of_endpoint
  · rw [data_18_169423.1]; exact data_18_169423.2.2
  · rw [data_18_169423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169503). -/
theorem data_18_169503 : oddCount 169503 18 = 11 ∧
    acceleratedOrbit 18 169503 = 114545 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169503 : ∀ j : Fin 18,
    169503 ≤ acceleratedOrbit j.val 169503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169503) = 177147 * m + 114545 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169503
  rw [data_18_169503.1, data_18_169503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169503) < 262144 * m + 169503 := by
  apply descent_of_endpoint
  · rw [data_18_169503.1]; exact data_18_169503.2.2
  · rw [data_18_169503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169631). -/
theorem data_18_169631 : oddCount 169631 18 = 11 ∧
    acceleratedOrbit 18 169631 = 114631 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169631 : ∀ j : Fin 18,
    169631 ≤ acceleratedOrbit j.val 169631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169631) = 177147 * m + 114631 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169631
  rw [data_18_169631.1, data_18_169631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169631) < 262144 * m + 169631 := by
  apply descent_of_endpoint
  · rw [data_18_169631.1]; exact data_18_169631.2.2
  · rw [data_18_169631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169663). -/
theorem data_18_169663 : oddCount 169663 18 = 11 ∧
    acceleratedOrbit 18 169663 = 114653 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169663 : ∀ j : Fin 18,
    169663 ≤ acceleratedOrbit j.val 169663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169663) = 177147 * m + 114653 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169663
  rw [data_18_169663.1, data_18_169663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169663) < 262144 * m + 169663 := by
  apply descent_of_endpoint
  · rw [data_18_169663.1]; exact data_18_169663.2.2
  · rw [data_18_169663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169703). -/
theorem data_18_169703 : oddCount 169703 18 = 11 ∧
    acceleratedOrbit 18 169703 = 114680 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169703 : ∀ j : Fin 18,
    169703 ≤ acceleratedOrbit j.val 169703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169703) = 177147 * m + 114680 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169703
  rw [data_18_169703.1, data_18_169703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169703) < 262144 * m + 169703 := by
  apply descent_of_endpoint
  · rw [data_18_169703.1]; exact data_18_169703.2.2
  · rw [data_18_169703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 170395). -/
theorem data_18_170395 : oddCount 170395 18 = 11 ∧
    acceleratedOrbit 18 170395 = 115148 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_170395 : ∀ j : Fin 18,
    170395 ≤ acceleratedOrbit j.val 170395 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_170395 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 170395) = 177147 * m + 115148 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 170395
  rw [data_18_170395.1, data_18_170395.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_170395 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 170395) < 262144 * m + 170395 := by
  apply descent_of_endpoint
  · rw [data_18_170395.1]; exact data_18_170395.2.2
  · rw [data_18_170395.2.1]; decide

end Collatz.Research.FirstDescent.Batch179
