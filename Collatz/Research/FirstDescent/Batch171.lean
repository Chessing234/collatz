import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 171. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch171
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 154159). -/
theorem data_18_154159 : oddCount 154159 18 = 11 ∧
    acceleratedOrbit 18 154159 = 104176 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_154159 : ∀ j : Fin 18,
    154159 ≤ acceleratedOrbit j.val 154159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_154159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154159) = 177147 * m + 104176 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 154159
  rw [data_18_154159.1, data_18_154159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_154159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154159) < 262144 * m + 154159 := by
  apply descent_of_endpoint
  · rw [data_18_154159.1]; exact data_18_154159.2.2
  · rw [data_18_154159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 154267). -/
theorem data_18_154267 : oddCount 154267 18 = 11 ∧
    acceleratedOrbit 18 154267 = 104249 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_154267 : ∀ j : Fin 18,
    154267 ≤ acceleratedOrbit j.val 154267 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_154267 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154267) = 177147 * m + 104249 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 154267
  rw [data_18_154267.1, data_18_154267.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_154267 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154267) < 262144 * m + 154267 := by
  apply descent_of_endpoint
  · rw [data_18_154267.1]; exact data_18_154267.2.2
  · rw [data_18_154267.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 154559). -/
theorem data_18_154559 : oddCount 154559 18 = 11 ∧
    acceleratedOrbit 18 154559 = 104446 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_154559 : ∀ j : Fin 18,
    154559 ≤ acceleratedOrbit j.val 154559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_154559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154559) = 177147 * m + 104446 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 154559
  rw [data_18_154559.1, data_18_154559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_154559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154559) < 262144 * m + 154559 := by
  apply descent_of_endpoint
  · rw [data_18_154559.1]; exact data_18_154559.2.2
  · rw [data_18_154559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 154591). -/
theorem data_18_154591 : oddCount 154591 18 = 11 ∧
    acceleratedOrbit 18 154591 = 104468 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_154591 : ∀ j : Fin 18,
    154591 ≤ acceleratedOrbit j.val 154591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_154591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154591) = 177147 * m + 104468 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 154591
  rw [data_18_154591.1, data_18_154591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_154591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154591) < 262144 * m + 154591 := by
  apply descent_of_endpoint
  · rw [data_18_154591.1]; exact data_18_154591.2.2
  · rw [data_18_154591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 154791). -/
theorem data_18_154791 : oddCount 154791 18 = 11 ∧
    acceleratedOrbit 18 154791 = 104603 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_154791 : ∀ j : Fin 18,
    154791 ≤ acceleratedOrbit j.val 154791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_154791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154791) = 177147 * m + 104603 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 154791
  rw [data_18_154791.1, data_18_154791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_154791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154791) < 262144 * m + 154791 := by
  apply descent_of_endpoint
  · rw [data_18_154791.1]; exact data_18_154791.2.2
  · rw [data_18_154791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 154927). -/
theorem data_18_154927 : oddCount 154927 18 = 11 ∧
    acceleratedOrbit 18 154927 = 104695 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_154927 : ∀ j : Fin 18,
    154927 ≤ acceleratedOrbit j.val 154927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_154927 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154927) = 177147 * m + 104695 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 154927
  rw [data_18_154927.1, data_18_154927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_154927 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 154927) < 262144 * m + 154927 := by
  apply descent_of_endpoint
  · rw [data_18_154927.1]; exact data_18_154927.2.2
  · rw [data_18_154927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 155167). -/
theorem data_18_155167 : oddCount 155167 18 = 11 ∧
    acceleratedOrbit 18 155167 = 104857 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_155167 : ∀ j : Fin 18,
    155167 ≤ acceleratedOrbit j.val 155167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_155167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155167) = 177147 * m + 104857 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 155167
  rw [data_18_155167.1, data_18_155167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_155167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155167) < 262144 * m + 155167 := by
  apply descent_of_endpoint
  · rw [data_18_155167.1]; exact data_18_155167.2.2
  · rw [data_18_155167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 155239). -/
theorem data_18_155239 : oddCount 155239 18 = 11 ∧
    acceleratedOrbit 18 155239 = 104906 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_155239 : ∀ j : Fin 18,
    155239 ≤ acceleratedOrbit j.val 155239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_155239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155239) = 177147 * m + 104906 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 155239
  rw [data_18_155239.1, data_18_155239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_155239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 155239) < 262144 * m + 155239 := by
  apply descent_of_endpoint
  · rw [data_18_155239.1]; exact data_18_155239.2.2
  · rw [data_18_155239.2.1]; decide

end Collatz.Research.FirstDescent.Batch171
