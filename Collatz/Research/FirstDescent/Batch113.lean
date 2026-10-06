import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 113. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch113
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27631). -/
theorem data_18_27631 : oddCount 27631 18 = 11 ∧
    acceleratedOrbit 18 27631 = 18673 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27631 : ∀ j : Fin 18,
    27631 ≤ acceleratedOrbit j.val 27631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27631) = 177147 * m + 18673 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27631
  rw [data_18_27631.1, data_18_27631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27631) < 262144 * m + 27631 := by
  apply descent_of_endpoint
  · rw [data_18_27631.1]; exact data_18_27631.2.2
  · rw [data_18_27631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 27751). -/
theorem data_18_27751 : oddCount 27751 18 = 11 ∧
    acceleratedOrbit 18 27751 = 18754 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_27751 : ∀ j : Fin 18,
    27751 ≤ acceleratedOrbit j.val 27751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_27751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27751) = 177147 * m + 18754 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 27751
  rw [data_18_27751.1, data_18_27751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_27751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 27751) < 262144 * m + 27751 := by
  apply descent_of_endpoint
  · rw [data_18_27751.1]; exact data_18_27751.2.2
  · rw [data_18_27751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 28063). -/
theorem data_18_28063 : oddCount 28063 18 = 11 ∧
    acceleratedOrbit 18 28063 = 18965 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_28063 : ∀ j : Fin 18,
    28063 ≤ acceleratedOrbit j.val 28063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_28063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28063) = 177147 * m + 18965 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 28063
  rw [data_18_28063.1, data_18_28063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_28063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28063) < 262144 * m + 28063 := by
  apply descent_of_endpoint
  · rw [data_18_28063.1]; exact data_18_28063.2.2
  · rw [data_18_28063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 28143). -/
theorem data_18_28143 : oddCount 28143 18 = 11 ∧
    acceleratedOrbit 18 28143 = 19019 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_28143 : ∀ j : Fin 18,
    28143 ≤ acceleratedOrbit j.val 28143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_28143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28143) = 177147 * m + 19019 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 28143
  rw [data_18_28143.1, data_18_28143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_28143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28143) < 262144 * m + 28143 := by
  apply descent_of_endpoint
  · rw [data_18_28143.1]; exact data_18_28143.2.2
  · rw [data_18_28143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 28187). -/
theorem data_18_28187 : oddCount 28187 18 = 11 ∧
    acceleratedOrbit 18 28187 = 19049 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_28187 : ∀ j : Fin 18,
    28187 ≤ acceleratedOrbit j.val 28187 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_28187 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28187) = 177147 * m + 19049 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 28187
  rw [data_18_28187.1, data_18_28187.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_28187 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28187) < 262144 * m + 28187 := by
  apply descent_of_endpoint
  · rw [data_18_28187.1]; exact data_18_28187.2.2
  · rw [data_18_28187.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 28955). -/
theorem data_18_28955 : oddCount 28955 18 = 11 ∧
    acceleratedOrbit 18 28955 = 19568 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_28955 : ∀ j : Fin 18,
    28955 ≤ acceleratedOrbit j.val 28955 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_28955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28955) = 177147 * m + 19568 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 28955
  rw [data_18_28955.1, data_18_28955.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_28955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 28955) < 262144 * m + 28955 := by
  apply descent_of_endpoint
  · rw [data_18_28955.1]; exact data_18_28955.2.2
  · rw [data_18_28955.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 29311). -/
theorem data_18_29311 : oddCount 29311 18 = 11 ∧
    acceleratedOrbit 18 29311 = 19808 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_29311 : ∀ j : Fin 18,
    29311 ≤ acceleratedOrbit j.val 29311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_29311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 29311) = 177147 * m + 19808 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 29311
  rw [data_18_29311.1, data_18_29311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_29311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 29311) < 262144 * m + 29311 := by
  apply descent_of_endpoint
  · rw [data_18_29311.1]; exact data_18_29311.2.2
  · rw [data_18_29311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 29799). -/
theorem data_18_29799 : oddCount 29799 18 = 11 ∧
    acceleratedOrbit 18 29799 = 20138 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_29799 : ∀ j : Fin 18,
    29799 ≤ acceleratedOrbit j.val 29799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_29799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 29799) = 177147 * m + 20138 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 29799
  rw [data_18_29799.1, data_18_29799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_29799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 29799) < 262144 * m + 29799 := by
  apply descent_of_endpoint
  · rw [data_18_29799.1]; exact data_18_29799.2.2
  · rw [data_18_29799.2.1]; decide

end Collatz.Research.FirstDescent.Batch113
