import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 178. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch178
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 168143). -/
theorem data_18_168143 : oddCount 168143 18 = 11 ∧
    acceleratedOrbit 18 168143 = 113626 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_168143 : ∀ j : Fin 18,
    168143 ≤ acceleratedOrbit j.val 168143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_168143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168143) = 177147 * m + 113626 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 168143
  rw [data_18_168143.1, data_18_168143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_168143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168143) < 262144 * m + 168143 := by
  apply descent_of_endpoint
  · rw [data_18_168143.1]; exact data_18_168143.2.2
  · rw [data_18_168143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 168263). -/
theorem data_18_168263 : oddCount 168263 18 = 11 ∧
    acceleratedOrbit 18 168263 = 113707 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_168263 : ∀ j : Fin 18,
    168263 ≤ acceleratedOrbit j.val 168263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_168263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168263) = 177147 * m + 113707 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 168263
  rw [data_18_168263.1, data_18_168263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_168263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168263) < 262144 * m + 168263 := by
  apply descent_of_endpoint
  · rw [data_18_168263.1]; exact data_18_168263.2.2
  · rw [data_18_168263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 168615). -/
theorem data_18_168615 : oddCount 168615 18 = 11 ∧
    acceleratedOrbit 18 168615 = 113945 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_168615 : ∀ j : Fin 18,
    168615 ≤ acceleratedOrbit j.val 168615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_168615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168615) = 177147 * m + 113945 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 168615
  rw [data_18_168615.1, data_18_168615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_168615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168615) < 262144 * m + 168615 := by
  apply descent_of_endpoint
  · rw [data_18_168615.1]; exact data_18_168615.2.2
  · rw [data_18_168615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 168655). -/
theorem data_18_168655 : oddCount 168655 18 = 11 ∧
    acceleratedOrbit 18 168655 = 113972 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_168655 : ∀ j : Fin 18,
    168655 ≤ acceleratedOrbit j.val 168655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_168655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168655) = 177147 * m + 113972 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 168655
  rw [data_18_168655.1, data_18_168655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_168655 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168655) < 262144 * m + 168655 := by
  apply descent_of_endpoint
  · rw [data_18_168655.1]; exact data_18_168655.2.2
  · rw [data_18_168655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 168735). -/
theorem data_18_168735 : oddCount 168735 18 = 11 ∧
    acceleratedOrbit 18 168735 = 114026 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_168735 : ∀ j : Fin 18,
    168735 ≤ acceleratedOrbit j.val 168735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_168735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168735) = 177147 * m + 114026 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 168735
  rw [data_18_168735.1, data_18_168735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_168735 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168735) < 262144 * m + 168735 := by
  apply descent_of_endpoint
  · rw [data_18_168735.1]; exact data_18_168735.2.2
  · rw [data_18_168735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 168775). -/
theorem data_18_168775 : oddCount 168775 18 = 11 ∧
    acceleratedOrbit 18 168775 = 114053 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_168775 : ∀ j : Fin 18,
    168775 ≤ acceleratedOrbit j.val 168775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_168775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168775) = 177147 * m + 114053 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 168775
  rw [data_18_168775.1, data_18_168775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_168775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 168775) < 262144 * m + 168775 := by
  apply descent_of_endpoint
  · rw [data_18_168775.1]; exact data_18_168775.2.2
  · rw [data_18_168775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169183). -/
theorem data_18_169183 : oddCount 169183 18 = 11 ∧
    acceleratedOrbit 18 169183 = 114329 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169183 : ∀ j : Fin 18,
    169183 ≤ acceleratedOrbit j.val 169183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169183) = 177147 * m + 114329 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169183
  rw [data_18_169183.1, data_18_169183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169183) < 262144 * m + 169183 := by
  apply descent_of_endpoint
  · rw [data_18_169183.1]; exact data_18_169183.2.2
  · rw [data_18_169183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 169191). -/
theorem data_18_169191 : oddCount 169191 18 = 11 ∧
    acceleratedOrbit 18 169191 = 114334 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_169191 : ∀ j : Fin 18,
    169191 ≤ acceleratedOrbit j.val 169191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_169191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169191) = 177147 * m + 114334 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 169191
  rw [data_18_169191.1, data_18_169191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_169191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 169191) < 262144 * m + 169191 := by
  apply descent_of_endpoint
  · rw [data_18_169191.1]; exact data_18_169191.2.2
  · rw [data_18_169191.2.1]; decide

end Collatz.Research.FirstDescent.Batch178
