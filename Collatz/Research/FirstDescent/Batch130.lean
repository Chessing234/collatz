import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 130. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch130
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 63259). -/
theorem data_18_63259 : oddCount 63259 18 = 11 ∧
    acceleratedOrbit 18 63259 = 42749 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_63259 : ∀ j : Fin 18,
    63259 ≤ acceleratedOrbit j.val 63259 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_63259 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63259) = 177147 * m + 42749 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 63259
  rw [data_18_63259.1, data_18_63259.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_63259 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63259) < 262144 * m + 63259 := by
  apply descent_of_endpoint
  · rw [data_18_63259.1]; exact data_18_63259.2.2
  · rw [data_18_63259.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 63343). -/
theorem data_18_63343 : oddCount 63343 18 = 11 ∧
    acceleratedOrbit 18 63343 = 42806 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_63343 : ∀ j : Fin 18,
    63343 ≤ acceleratedOrbit j.val 63343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_63343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63343) = 177147 * m + 42806 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 63343
  rw [data_18_63343.1, data_18_63343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_63343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63343) < 262144 * m + 63343 := by
  apply descent_of_endpoint
  · rw [data_18_63343.1]; exact data_18_63343.2.2
  · rw [data_18_63343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 63423). -/
theorem data_18_63423 : oddCount 63423 18 = 11 ∧
    acceleratedOrbit 18 63423 = 42860 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_63423 : ∀ j : Fin 18,
    63423 ≤ acceleratedOrbit j.val 63423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_63423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63423) = 177147 * m + 42860 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 63423
  rw [data_18_63423.1, data_18_63423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_63423 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63423) < 262144 * m + 63423 := by
  apply descent_of_endpoint
  · rw [data_18_63423.1]; exact data_18_63423.2.2
  · rw [data_18_63423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 63743). -/
theorem data_18_63743 : oddCount 63743 18 = 11 ∧
    acceleratedOrbit 18 63743 = 43076 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_63743 : ∀ j : Fin 18,
    63743 ≤ acceleratedOrbit j.val 63743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_63743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63743) = 177147 * m + 43076 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 63743
  rw [data_18_63743.1, data_18_63743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_63743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 63743) < 262144 * m + 63743 := by
  apply descent_of_endpoint
  · rw [data_18_63743.1]; exact data_18_63743.2.2
  · rw [data_18_63743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 64283). -/
theorem data_18_64283 : oddCount 64283 18 = 11 ∧
    acceleratedOrbit 18 64283 = 43441 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_64283 : ∀ j : Fin 18,
    64283 ≤ acceleratedOrbit j.val 64283 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_64283 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 64283) = 177147 * m + 43441 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 64283
  rw [data_18_64283.1, data_18_64283.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_64283 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 64283) < 262144 * m + 64283 := by
  apply descent_of_endpoint
  · rw [data_18_64283.1]; exact data_18_64283.2.2
  · rw [data_18_64283.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 64671). -/
theorem data_18_64671 : oddCount 64671 18 = 11 ∧
    acceleratedOrbit 18 64671 = 43703 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_64671 : ∀ j : Fin 18,
    64671 ≤ acceleratedOrbit j.val 64671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_64671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 64671) = 177147 * m + 43703 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 64671
  rw [data_18_64671.1, data_18_64671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_64671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 64671) < 262144 * m + 64671 := by
  apply descent_of_endpoint
  · rw [data_18_64671.1]; exact data_18_64671.2.2
  · rw [data_18_64671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 65531). -/
theorem data_18_65531 : oddCount 65531 18 = 11 ∧
    acceleratedOrbit 18 65531 = 44285 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_65531 : ∀ j : Fin 18,
    65531 ≤ acceleratedOrbit j.val 65531 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_65531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 65531) = 177147 * m + 44285 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 65531
  rw [data_18_65531.1, data_18_65531.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_65531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 65531) < 262144 * m + 65531 := by
  apply descent_of_endpoint
  · rw [data_18_65531.1]; exact data_18_65531.2.2
  · rw [data_18_65531.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 65691). -/
theorem data_18_65691 : oddCount 65691 18 = 11 ∧
    acceleratedOrbit 18 65691 = 44393 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_65691 : ∀ j : Fin 18,
    65691 ≤ acceleratedOrbit j.val 65691 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_65691 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 65691) = 177147 * m + 44393 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 65691
  rw [data_18_65691.1, data_18_65691.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_65691 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 65691) < 262144 * m + 65691 := by
  apply descent_of_endpoint
  · rw [data_18_65691.1]; exact data_18_65691.2.2
  · rw [data_18_65691.2.1]; decide

end Collatz.Research.FirstDescent.Batch130
