import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 217. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch217
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 257691). -/
theorem data_18_257691 : oddCount 257691 18 = 11 ∧
    acceleratedOrbit 18 257691 = 174139 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_257691 : ∀ j : Fin 18,
    257691 ≤ acceleratedOrbit j.val 257691 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_257691 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257691) = 177147 * m + 174139 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 257691
  rw [data_18_257691.1, data_18_257691.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_257691 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257691) < 262144 * m + 257691 := by
  apply descent_of_endpoint
  · rw [data_18_257691.1]; exact data_18_257691.2.2
  · rw [data_18_257691.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 257883). -/
theorem data_18_257883 : oddCount 257883 18 = 11 ∧
    acceleratedOrbit 18 257883 = 174269 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_257883 : ∀ j : Fin 18,
    257883 ≤ acceleratedOrbit j.val 257883 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_257883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257883) = 177147 * m + 174269 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 257883
  rw [data_18_257883.1, data_18_257883.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_257883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 257883) < 262144 * m + 257883 := by
  apply descent_of_endpoint
  · rw [data_18_257883.1]; exact data_18_257883.2.2
  · rw [data_18_257883.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 258095). -/
theorem data_18_258095 : oddCount 258095 18 = 11 ∧
    acceleratedOrbit 18 258095 = 174412 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_258095 : ∀ j : Fin 18,
    258095 ≤ acceleratedOrbit j.val 258095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_258095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258095) = 177147 * m + 174412 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 258095
  rw [data_18_258095.1, data_18_258095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_258095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258095) < 262144 * m + 258095 := by
  apply descent_of_endpoint
  · rw [data_18_258095.1]; exact data_18_258095.2.2
  · rw [data_18_258095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 258159). -/
theorem data_18_258159 : oddCount 258159 18 = 11 ∧
    acceleratedOrbit 18 258159 = 174455 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_258159 : ∀ j : Fin 18,
    258159 ≤ acceleratedOrbit j.val 258159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_258159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258159) = 177147 * m + 174455 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 258159
  rw [data_18_258159.1, data_18_258159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_258159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258159) < 262144 * m + 258159 := by
  apply descent_of_endpoint
  · rw [data_18_258159.1]; exact data_18_258159.2.2
  · rw [data_18_258159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 258215). -/
theorem data_18_258215 : oddCount 258215 18 = 11 ∧
    acceleratedOrbit 18 258215 = 174493 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_258215 : ∀ j : Fin 18,
    258215 ≤ acceleratedOrbit j.val 258215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_258215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258215) = 177147 * m + 174493 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 258215
  rw [data_18_258215.1, data_18_258215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_258215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258215) < 262144 * m + 258215 := by
  apply descent_of_endpoint
  · rw [data_18_258215.1]; exact data_18_258215.2.2
  · rw [data_18_258215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 258495). -/
theorem data_18_258495 : oddCount 258495 18 = 11 ∧
    acceleratedOrbit 18 258495 = 174682 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_258495 : ∀ j : Fin 18,
    258495 ≤ acceleratedOrbit j.val 258495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_258495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258495) = 177147 * m + 174682 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 258495
  rw [data_18_258495.1, data_18_258495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_258495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258495) < 262144 * m + 258495 := by
  apply descent_of_endpoint
  · rw [data_18_258495.1]; exact data_18_258495.2.2
  · rw [data_18_258495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 258607). -/
theorem data_18_258607 : oddCount 258607 18 = 11 ∧
    acceleratedOrbit 18 258607 = 174758 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_258607 : ∀ j : Fin 18,
    258607 ≤ acceleratedOrbit j.val 258607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_258607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258607) = 177147 * m + 174758 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 258607
  rw [data_18_258607.1, data_18_258607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_258607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 258607) < 262144 * m + 258607 := by
  apply descent_of_endpoint
  · rw [data_18_258607.1]; exact data_18_258607.2.2
  · rw [data_18_258607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 259007). -/
theorem data_18_259007 : oddCount 259007 18 = 11 ∧
    acceleratedOrbit 18 259007 = 175028 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_259007 : ∀ j : Fin 18,
    259007 ≤ acceleratedOrbit j.val 259007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_259007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 259007) = 177147 * m + 175028 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 259007
  rw [data_18_259007.1, data_18_259007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_259007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 259007) < 262144 * m + 259007 := by
  apply descent_of_endpoint
  · rw [data_18_259007.1]; exact data_18_259007.2.2
  · rw [data_18_259007.2.1]; decide

end Collatz.Research.FirstDescent.Batch217
