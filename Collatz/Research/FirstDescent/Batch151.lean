import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 151. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch151
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 108123). -/
theorem data_18_108123 : oddCount 108123 18 = 11 ∧
    acceleratedOrbit 18 108123 = 73067 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_108123 : ∀ j : Fin 18,
    108123 ≤ acceleratedOrbit j.val 108123 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_108123 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108123) = 177147 * m + 73067 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 108123
  rw [data_18_108123.1, data_18_108123.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_108123 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108123) < 262144 * m + 108123 := by
  apply descent_of_endpoint
  · rw [data_18_108123.1]; exact data_18_108123.2.2
  · rw [data_18_108123.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 108239). -/
theorem data_18_108239 : oddCount 108239 18 = 11 ∧
    acceleratedOrbit 18 108239 = 73145 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_108239 : ∀ j : Fin 18,
    108239 ≤ acceleratedOrbit j.val 108239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_108239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108239) = 177147 * m + 73145 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 108239
  rw [data_18_108239.1, data_18_108239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_108239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108239) < 262144 * m + 108239 := by
  apply descent_of_endpoint
  · rw [data_18_108239.1]; exact data_18_108239.2.2
  · rw [data_18_108239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 108287). -/
theorem data_18_108287 : oddCount 108287 18 = 11 ∧
    acceleratedOrbit 18 108287 = 73177 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_108287 : ∀ j : Fin 18,
    108287 ≤ acceleratedOrbit j.val 108287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_108287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108287) = 177147 * m + 73177 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 108287
  rw [data_18_108287.1, data_18_108287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_108287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108287) < 262144 * m + 108287 := by
  apply descent_of_endpoint
  · rw [data_18_108287.1]; exact data_18_108287.2.2
  · rw [data_18_108287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 108539). -/
theorem data_18_108539 : oddCount 108539 18 = 11 ∧
    acceleratedOrbit 18 108539 = 73348 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_108539 : ∀ j : Fin 18,
    108539 ≤ acceleratedOrbit j.val 108539 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_108539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108539) = 177147 * m + 73348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 108539
  rw [data_18_108539.1, data_18_108539.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_108539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108539) < 262144 * m + 108539 := by
  apply descent_of_endpoint
  · rw [data_18_108539.1]; exact data_18_108539.2.2
  · rw [data_18_108539.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 109211). -/
theorem data_18_109211 : oddCount 109211 18 = 11 ∧
    acceleratedOrbit 18 109211 = 73802 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_109211 : ∀ j : Fin 18,
    109211 ≤ acceleratedOrbit j.val 109211 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_109211 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109211) = 177147 * m + 73802 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 109211
  rw [data_18_109211.1, data_18_109211.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_109211 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109211) < 262144 * m + 109211 := by
  apply descent_of_endpoint
  · rw [data_18_109211.1]; exact data_18_109211.2.2
  · rw [data_18_109211.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 109223). -/
theorem data_18_109223 : oddCount 109223 18 = 11 ∧
    acceleratedOrbit 18 109223 = 73810 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_109223 : ∀ j : Fin 18,
    109223 ≤ acceleratedOrbit j.val 109223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_109223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109223) = 177147 * m + 73810 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 109223
  rw [data_18_109223.1, data_18_109223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_109223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109223) < 262144 * m + 109223 := by
  apply descent_of_endpoint
  · rw [data_18_109223.1]; exact data_18_109223.2.2
  · rw [data_18_109223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 109263). -/
theorem data_18_109263 : oddCount 109263 18 = 11 ∧
    acceleratedOrbit 18 109263 = 73837 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_109263 : ∀ j : Fin 18,
    109263 ≤ acceleratedOrbit j.val 109263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_109263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109263) = 177147 * m + 73837 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 109263
  rw [data_18_109263.1, data_18_109263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_109263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109263) < 262144 * m + 109263 := by
  apply descent_of_endpoint
  · rw [data_18_109263.1]; exact data_18_109263.2.2
  · rw [data_18_109263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 109287). -/
theorem data_18_109287 : oddCount 109287 18 = 11 ∧
    acceleratedOrbit 18 109287 = 73853 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_109287 : ∀ j : Fin 18,
    109287 ≤ acceleratedOrbit j.val 109287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_109287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109287) = 177147 * m + 73853 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 109287
  rw [data_18_109287.1, data_18_109287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_109287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 109287) < 262144 * m + 109287 := by
  apply descent_of_endpoint
  · rw [data_18_109287.1]; exact data_18_109287.2.2
  · rw [data_18_109287.2.1]; decide

end Collatz.Research.FirstDescent.Batch151
