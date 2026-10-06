import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 185. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch185
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 182119). -/
theorem data_18_182119 : oddCount 182119 18 = 11 ∧
    acceleratedOrbit 18 182119 = 123070 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_182119 : ∀ j : Fin 18,
    182119 ≤ acceleratedOrbit j.val 182119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_182119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182119) = 177147 * m + 123070 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 182119
  rw [data_18_182119.1, data_18_182119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_182119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182119) < 262144 * m + 182119 := by
  apply descent_of_endpoint
  · rw [data_18_182119.1]; exact data_18_182119.2.2
  · rw [data_18_182119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 182687). -/
theorem data_18_182687 : oddCount 182687 18 = 11 ∧
    acceleratedOrbit 18 182687 = 123454 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_182687 : ∀ j : Fin 18,
    182687 ≤ acceleratedOrbit j.val 182687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_182687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182687) = 177147 * m + 123454 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 182687
  rw [data_18_182687.1, data_18_182687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_182687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182687) < 262144 * m + 182687 := by
  apply descent_of_endpoint
  · rw [data_18_182687.1]; exact data_18_182687.2.2
  · rw [data_18_182687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 182759). -/
theorem data_18_182759 : oddCount 182759 18 = 11 ∧
    acceleratedOrbit 18 182759 = 123503 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_182759 : ∀ j : Fin 18,
    182759 ≤ acceleratedOrbit j.val 182759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_182759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182759) = 177147 * m + 123503 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 182759
  rw [data_18_182759.1, data_18_182759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_182759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182759) < 262144 * m + 182759 := by
  apply descent_of_endpoint
  · rw [data_18_182759.1]; exact data_18_182759.2.2
  · rw [data_18_182759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 182767). -/
theorem data_18_182767 : oddCount 182767 18 = 11 ∧
    acceleratedOrbit 18 182767 = 123508 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_182767 : ∀ j : Fin 18,
    182767 ≤ acceleratedOrbit j.val 182767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_182767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182767) = 177147 * m + 123508 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 182767
  rw [data_18_182767.1, data_18_182767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_182767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182767) < 262144 * m + 182767 := by
  apply descent_of_endpoint
  · rw [data_18_182767.1]; exact data_18_182767.2.2
  · rw [data_18_182767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 183207). -/
theorem data_18_183207 : oddCount 183207 18 = 11 ∧
    acceleratedOrbit 18 183207 = 123806 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_183207 : ∀ j : Fin 18,
    183207 ≤ acceleratedOrbit j.val 183207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_183207 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183207) = 177147 * m + 123806 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 183207
  rw [data_18_183207.1, data_18_183207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_183207 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183207) < 262144 * m + 183207 := by
  apply descent_of_endpoint
  · rw [data_18_183207.1]; exact data_18_183207.2.2
  · rw [data_18_183207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 183279). -/
theorem data_18_183279 : oddCount 183279 18 = 11 ∧
    acceleratedOrbit 18 183279 = 123854 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_183279 : ∀ j : Fin 18,
    183279 ≤ acceleratedOrbit j.val 183279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_183279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183279) = 177147 * m + 123854 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 183279
  rw [data_18_183279.1, data_18_183279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_183279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183279) < 262144 * m + 183279 := by
  apply descent_of_endpoint
  · rw [data_18_183279.1]; exact data_18_183279.2.2
  · rw [data_18_183279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 183527). -/
theorem data_18_183527 : oddCount 183527 18 = 11 ∧
    acceleratedOrbit 18 183527 = 124022 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_183527 : ∀ j : Fin 18,
    183527 ≤ acceleratedOrbit j.val 183527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_183527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183527) = 177147 * m + 124022 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 183527
  rw [data_18_183527.1, data_18_183527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_183527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183527) < 262144 * m + 183527 := by
  apply descent_of_endpoint
  · rw [data_18_183527.1]; exact data_18_183527.2.2
  · rw [data_18_183527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 183615). -/
theorem data_18_183615 : oddCount 183615 18 = 11 ∧
    acceleratedOrbit 18 183615 = 124081 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_183615 : ∀ j : Fin 18,
    183615 ≤ acceleratedOrbit j.val 183615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_183615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183615) = 177147 * m + 124081 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 183615
  rw [data_18_183615.1, data_18_183615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_183615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 183615) < 262144 * m + 183615 := by
  apply descent_of_endpoint
  · rw [data_18_183615.1]; exact data_18_183615.2.2
  · rw [data_18_183615.2.1]; decide

end Collatz.Research.FirstDescent.Batch185
