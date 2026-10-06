import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 119. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch119
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 42367). -/
theorem data_18_42367 : oddCount 42367 18 = 11 ∧
    acceleratedOrbit 18 42367 = 28631 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_42367 : ∀ j : Fin 18,
    42367 ≤ acceleratedOrbit j.val 42367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_42367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 42367) = 177147 * m + 28631 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 42367
  rw [data_18_42367.1, data_18_42367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_42367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 42367) < 262144 * m + 42367 := by
  apply descent_of_endpoint
  · rw [data_18_42367.1]; exact data_18_42367.2.2
  · rw [data_18_42367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 43455). -/
theorem data_18_43455 : oddCount 43455 18 = 11 ∧
    acceleratedOrbit 18 43455 = 29366 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_43455 : ∀ j : Fin 18,
    43455 ≤ acceleratedOrbit j.val 43455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_43455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 43455) = 177147 * m + 29366 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 43455
  rw [data_18_43455.1, data_18_43455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_43455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 43455) < 262144 * m + 43455 := by
  apply descent_of_endpoint
  · rw [data_18_43455.1]; exact data_18_43455.2.2
  · rw [data_18_43455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 44063). -/
theorem data_18_44063 : oddCount 44063 18 = 11 ∧
    acceleratedOrbit 18 44063 = 29777 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_44063 : ∀ j : Fin 18,
    44063 ≤ acceleratedOrbit j.val 44063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_44063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44063) = 177147 * m + 29777 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 44063
  rw [data_18_44063.1, data_18_44063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_44063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44063) < 262144 * m + 44063 := by
  apply descent_of_endpoint
  · rw [data_18_44063.1]; exact data_18_44063.2.2
  · rw [data_18_44063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 44123). -/
theorem data_18_44123 : oddCount 44123 18 = 11 ∧
    acceleratedOrbit 18 44123 = 29818 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_44123 : ∀ j : Fin 18,
    44123 ≤ acceleratedOrbit j.val 44123 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_44123 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44123) = 177147 * m + 29818 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 44123
  rw [data_18_44123.1, data_18_44123.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_44123 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44123) < 262144 * m + 44123 := by
  apply descent_of_endpoint
  · rw [data_18_44123.1]; exact data_18_44123.2.2
  · rw [data_18_44123.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 44479). -/
theorem data_18_44479 : oddCount 44479 18 = 11 ∧
    acceleratedOrbit 18 44479 = 30058 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_44479 : ∀ j : Fin 18,
    44479 ≤ acceleratedOrbit j.val 44479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_44479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44479) = 177147 * m + 30058 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 44479
  rw [data_18_44479.1, data_18_44479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_44479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44479) < 262144 * m + 44479 := by
  apply descent_of_endpoint
  · rw [data_18_44479.1]; exact data_18_44479.2.2
  · rw [data_18_44479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 44591). -/
theorem data_18_44591 : oddCount 44591 18 = 11 ∧
    acceleratedOrbit 18 44591 = 30134 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_44591 : ∀ j : Fin 18,
    44591 ≤ acceleratedOrbit j.val 44591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_44591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44591) = 177147 * m + 30134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 44591
  rw [data_18_44591.1, data_18_44591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_44591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44591) < 262144 * m + 44591 := by
  apply descent_of_endpoint
  · rw [data_18_44591.1]; exact data_18_44591.2.2
  · rw [data_18_44591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 44891). -/
theorem data_18_44891 : oddCount 44891 18 = 11 ∧
    acceleratedOrbit 18 44891 = 30337 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_44891 : ∀ j : Fin 18,
    44891 ≤ acceleratedOrbit j.val 44891 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_44891 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44891) = 177147 * m + 30337 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 44891
  rw [data_18_44891.1, data_18_44891.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_44891 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 44891) < 262144 * m + 44891 := by
  apply descent_of_endpoint
  · rw [data_18_44891.1]; exact data_18_44891.2.2
  · rw [data_18_44891.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 45615). -/
theorem data_18_45615 : oddCount 45615 18 = 11 ∧
    acceleratedOrbit 18 45615 = 30826 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_45615 : ∀ j : Fin 18,
    45615 ≤ acceleratedOrbit j.val 45615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_45615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 45615) = 177147 * m + 30826 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 45615
  rw [data_18_45615.1, data_18_45615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_45615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 45615) < 262144 * m + 45615 := by
  apply descent_of_endpoint
  · rw [data_18_45615.1]; exact data_18_45615.2.2
  · rw [data_18_45615.2.1]; decide

end Collatz.Research.FirstDescent.Batch119
