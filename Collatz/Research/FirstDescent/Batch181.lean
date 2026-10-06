import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 181. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch181
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 173471). -/
theorem data_18_173471 : oddCount 173471 18 = 11 ∧
    acceleratedOrbit 18 173471 = 117226 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_173471 : ∀ j : Fin 18,
    173471 ≤ acceleratedOrbit j.val 173471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_173471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173471) = 177147 * m + 117226 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 173471
  rw [data_18_173471.1, data_18_173471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_173471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173471) < 262144 * m + 173471 := by
  apply descent_of_endpoint
  · rw [data_18_173471.1]; exact data_18_173471.2.2
  · rw [data_18_173471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 173991). -/
theorem data_18_173991 : oddCount 173991 18 = 11 ∧
    acceleratedOrbit 18 173991 = 117578 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_173991 : ∀ j : Fin 18,
    173991 ≤ acceleratedOrbit j.val 173991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_173991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173991) = 177147 * m + 117578 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 173991
  rw [data_18_173991.1, data_18_173991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_173991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173991) < 262144 * m + 173991 := by
  apply descent_of_endpoint
  · rw [data_18_173991.1]; exact data_18_173991.2.2
  · rw [data_18_173991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 174319). -/
theorem data_18_174319 : oddCount 174319 18 = 11 ∧
    acceleratedOrbit 18 174319 = 117799 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_174319 : ∀ j : Fin 18,
    174319 ≤ acceleratedOrbit j.val 174319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_174319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 174319) = 177147 * m + 117799 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 174319
  rw [data_18_174319.1, data_18_174319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_174319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 174319) < 262144 * m + 174319 := by
  apply descent_of_endpoint
  · rw [data_18_174319.1]; exact data_18_174319.2.2
  · rw [data_18_174319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 174875). -/
theorem data_18_174875 : oddCount 174875 18 = 11 ∧
    acceleratedOrbit 18 174875 = 118175 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_174875 : ∀ j : Fin 18,
    174875 ≤ acceleratedOrbit j.val 174875 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_174875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 174875) = 177147 * m + 118175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 174875
  rw [data_18_174875.1, data_18_174875.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_174875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 174875) < 262144 * m + 174875 := by
  apply descent_of_endpoint
  · rw [data_18_174875.1]; exact data_18_174875.2.2
  · rw [data_18_174875.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 175015). -/
theorem data_18_175015 : oddCount 175015 18 = 11 ∧
    acceleratedOrbit 18 175015 = 118270 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_175015 : ∀ j : Fin 18,
    175015 ≤ acceleratedOrbit j.val 175015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_175015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175015) = 177147 * m + 118270 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 175015
  rw [data_18_175015.1, data_18_175015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_175015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175015) < 262144 * m + 175015 := by
  apply descent_of_endpoint
  · rw [data_18_175015.1]; exact data_18_175015.2.2
  · rw [data_18_175015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 175131). -/
theorem data_18_175131 : oddCount 175131 18 = 11 ∧
    acceleratedOrbit 18 175131 = 118348 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_175131 : ∀ j : Fin 18,
    175131 ≤ acceleratedOrbit j.val 175131 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_175131 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175131) = 177147 * m + 118348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 175131
  rw [data_18_175131.1, data_18_175131.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_175131 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175131) < 262144 * m + 175131 := by
  apply descent_of_endpoint
  · rw [data_18_175131.1]; exact data_18_175131.2.2
  · rw [data_18_175131.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 175335). -/
theorem data_18_175335 : oddCount 175335 18 = 11 ∧
    acceleratedOrbit 18 175335 = 118486 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_175335 : ∀ j : Fin 18,
    175335 ≤ acceleratedOrbit j.val 175335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_175335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175335) = 177147 * m + 118486 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 175335
  rw [data_18_175335.1, data_18_175335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_175335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175335) < 262144 * m + 175335 := by
  apply descent_of_endpoint
  · rw [data_18_175335.1]; exact data_18_175335.2.2
  · rw [data_18_175335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 175567). -/
theorem data_18_175567 : oddCount 175567 18 = 11 ∧
    acceleratedOrbit 18 175567 = 118643 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_175567 : ∀ j : Fin 18,
    175567 ≤ acceleratedOrbit j.val 175567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_175567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175567) = 177147 * m + 118643 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 175567
  rw [data_18_175567.1, data_18_175567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_175567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175567) < 262144 * m + 175567 := by
  apply descent_of_endpoint
  · rw [data_18_175567.1]; exact data_18_175567.2.2
  · rw [data_18_175567.2.1]; decide

end Collatz.Research.FirstDescent.Batch181
