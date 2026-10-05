import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 115. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch115
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 32103). -/
theorem data_18_32103 : oddCount 32103 18 = 11 ∧
    acceleratedOrbit 18 32103 = 21695 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_32103 : ∀ j : Fin 18,
    32103 ≤ acceleratedOrbit j.val 32103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_32103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 32103) = 177147 * m + 21695 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 32103
  rw [data_18_32103.1, data_18_32103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_32103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 32103) < 262144 * m + 32103 := by
  apply descent_of_endpoint
  · rw [data_18_32103.1]; exact data_18_32103.2.2
  · rw [data_18_32103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 32671). -/
theorem data_18_32671 : oddCount 32671 18 = 11 ∧
    acceleratedOrbit 18 32671 = 22079 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_32671 : ∀ j : Fin 18,
    32671 ≤ acceleratedOrbit j.val 32671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_32671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 32671) = 177147 * m + 22079 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 32671
  rw [data_18_32671.1, data_18_32671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_32671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 32671) < 262144 * m + 32671 := by
  apply descent_of_endpoint
  · rw [data_18_32671.1]; exact data_18_32671.2.2
  · rw [data_18_32671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 33695). -/
theorem data_18_33695 : oddCount 33695 18 = 11 ∧
    acceleratedOrbit 18 33695 = 22771 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_33695 : ∀ j : Fin 18,
    33695 ≤ acceleratedOrbit j.val 33695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_33695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 33695) = 177147 * m + 22771 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 33695
  rw [data_18_33695.1, data_18_33695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_33695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 33695) < 262144 * m + 33695 := by
  apply descent_of_endpoint
  · rw [data_18_33695.1]; exact data_18_33695.2.2
  · rw [data_18_33695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 33775). -/
theorem data_18_33775 : oddCount 33775 18 = 11 ∧
    acceleratedOrbit 18 33775 = 22825 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_33775 : ∀ j : Fin 18,
    33775 ≤ acceleratedOrbit j.val 33775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_33775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 33775) = 177147 * m + 22825 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 33775
  rw [data_18_33775.1, data_18_33775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_33775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 33775) < 262144 * m + 33775 := by
  apply descent_of_endpoint
  · rw [data_18_33775.1]; exact data_18_33775.2.2
  · rw [data_18_33775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 33895). -/
theorem data_18_33895 : oddCount 33895 18 = 11 ∧
    acceleratedOrbit 18 33895 = 22906 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_33895 : ∀ j : Fin 18,
    33895 ≤ acceleratedOrbit j.val 33895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_33895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 33895) = 177147 * m + 22906 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 33895
  rw [data_18_33895.1, data_18_33895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_33895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 33895) < 262144 * m + 33895 := by
  apply descent_of_endpoint
  · rw [data_18_33895.1]; exact data_18_33895.2.2
  · rw [data_18_33895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 34287). -/
theorem data_18_34287 : oddCount 34287 18 = 11 ∧
    acceleratedOrbit 18 34287 = 23171 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_34287 : ∀ j : Fin 18,
    34287 ≤ acceleratedOrbit j.val 34287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_34287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34287) = 177147 * m + 23171 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 34287
  rw [data_18_34287.1, data_18_34287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_34287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34287) < 262144 * m + 34287 := by
  apply descent_of_endpoint
  · rw [data_18_34287.1]; exact data_18_34287.2.2
  · rw [data_18_34287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 34407). -/
theorem data_18_34407 : oddCount 34407 18 = 11 ∧
    acceleratedOrbit 18 34407 = 23252 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_34407 : ∀ j : Fin 18,
    34407 ≤ acceleratedOrbit j.val 34407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_34407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34407) = 177147 * m + 23252 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 34407
  rw [data_18_34407.1, data_18_34407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_34407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34407) < 262144 * m + 34407 := by
  apply descent_of_endpoint
  · rw [data_18_34407.1]; exact data_18_34407.2.2
  · rw [data_18_34407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 34687). -/
theorem data_18_34687 : oddCount 34687 18 = 11 ∧
    acceleratedOrbit 18 34687 = 23441 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_34687 : ∀ j : Fin 18,
    34687 ≤ acceleratedOrbit j.val 34687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_34687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34687) = 177147 * m + 23441 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 34687
  rw [data_18_34687.1, data_18_34687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_34687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34687) < 262144 * m + 34687 := by
  apply descent_of_endpoint
  · rw [data_18_34687.1]; exact data_18_34687.2.2
  · rw [data_18_34687.2.1]; decide

end Collatz.Research.FirstDescent.Batch115
