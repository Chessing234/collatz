import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 28. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch028
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 13567). -/
theorem data_15_13567 : oddCount 13567 15 = 9 ∧
    acceleratedOrbit 15 13567 = 8150 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_13567 : ∀ j : Fin 15,
    13567 ≤ acceleratedOrbit j.val 13567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_13567 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13567) = 19683 * m + 8150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 13567
  rw [data_15_13567.1, data_15_13567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_13567 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13567) < 32768 * m + 13567 := by
  apply descent_of_endpoint
  · rw [data_15_13567.1]; exact data_15_13567.2.2
  · rw [data_15_13567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 13695). -/
theorem data_15_13695 : oddCount 13695 15 = 9 ∧
    acceleratedOrbit 15 13695 = 8227 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_13695 : ∀ j : Fin 15,
    13695 ≤ acceleratedOrbit j.val 13695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_13695 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13695) = 19683 * m + 8227 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 13695
  rw [data_15_13695.1, data_15_13695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_13695 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13695) < 32768 * m + 13695 := by
  apply descent_of_endpoint
  · rw [data_15_13695.1]; exact data_15_13695.2.2
  · rw [data_15_13695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 13851). -/
theorem data_15_13851 : oddCount 13851 15 = 9 ∧
    acceleratedOrbit 15 13851 = 8321 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_13851 : ∀ j : Fin 15,
    13851 ≤ acceleratedOrbit j.val 13851 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_13851 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13851) = 19683 * m + 8321 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 13851
  rw [data_15_13851.1, data_15_13851.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_13851 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 13851) < 32768 * m + 13851 := by
  apply descent_of_endpoint
  · rw [data_15_13851.1]; exact data_15_13851.2.2
  · rw [data_15_13851.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 14031). -/
theorem data_15_14031 : oddCount 14031 15 = 9 ∧
    acceleratedOrbit 15 14031 = 8429 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_14031 : ∀ j : Fin 15,
    14031 ≤ acceleratedOrbit j.val 14031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_14031 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14031) = 19683 * m + 8429 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 14031
  rw [data_15_14031.1, data_15_14031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_14031 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14031) < 32768 * m + 14031 := by
  apply descent_of_endpoint
  · rw [data_15_14031.1]; exact data_15_14031.2.2
  · rw [data_15_14031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 14271). -/
theorem data_15_14271 : oddCount 14271 15 = 9 ∧
    acceleratedOrbit 15 14271 = 8573 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_14271 : ∀ j : Fin 15,
    14271 ≤ acceleratedOrbit j.val 14271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_14271 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14271) = 19683 * m + 8573 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 14271
  rw [data_15_14271.1, data_15_14271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_14271 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14271) < 32768 * m + 14271 := by
  apply descent_of_endpoint
  · rw [data_15_14271.1]; exact data_15_14271.2.2
  · rw [data_15_14271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 14399). -/
theorem data_15_14399 : oddCount 14399 15 = 9 ∧
    acceleratedOrbit 15 14399 = 8650 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_14399 : ∀ j : Fin 15,
    14399 ≤ acceleratedOrbit j.val 14399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_14399 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14399) = 19683 * m + 8650 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 14399
  rw [data_15_14399.1, data_15_14399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_14399 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14399) < 32768 * m + 14399 := by
  apply descent_of_endpoint
  · rw [data_15_14399.1]; exact data_15_14399.2.2
  · rw [data_15_14399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 14439). -/
theorem data_15_14439 : oddCount 14439 15 = 9 ∧
    acceleratedOrbit 15 14439 = 8674 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_14439 : ∀ j : Fin 15,
    14439 ≤ acceleratedOrbit j.val 14439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_14439 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14439) = 19683 * m + 8674 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 14439
  rw [data_15_14439.1, data_15_14439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_14439 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14439) < 32768 * m + 14439 := by
  apply descent_of_endpoint
  · rw [data_15_14439.1]; exact data_15_14439.2.2
  · rw [data_15_14439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 14895). -/
theorem data_15_14895 : oddCount 14895 15 = 9 ∧
    acceleratedOrbit 15 14895 = 8948 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_14895 : ∀ j : Fin 15,
    14895 ≤ acceleratedOrbit j.val 14895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_14895 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14895) = 19683 * m + 8948 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 14895
  rw [data_15_14895.1, data_15_14895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_14895 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 14895) < 32768 * m + 14895 := by
  apply descent_of_endpoint
  · rw [data_15_14895.1]; exact data_15_14895.2.2
  · rw [data_15_14895.2.1]; decide

end Collatz.Research.FirstDescent.Batch028
