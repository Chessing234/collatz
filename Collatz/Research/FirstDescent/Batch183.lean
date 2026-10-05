import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 183. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch183
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 176623). -/
theorem data_18_176623 : oddCount 176623 18 = 11 ∧
    acceleratedOrbit 18 176623 = 119356 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_176623 : ∀ j : Fin 18,
    176623 ≤ acceleratedOrbit j.val 176623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_176623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176623) = 177147 * m + 119356 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 176623
  rw [data_18_176623.1, data_18_176623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_176623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176623) < 262144 * m + 176623 := by
  apply descent_of_endpoint
  · rw [data_18_176623.1]; exact data_18_176623.2.2
  · rw [data_18_176623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 177179). -/
theorem data_18_177179 : oddCount 177179 18 = 11 ∧
    acceleratedOrbit 18 177179 = 119732 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_177179 : ∀ j : Fin 18,
    177179 ≤ acceleratedOrbit j.val 177179 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_177179 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 177179) = 177147 * m + 119732 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 177179
  rw [data_18_177179.1, data_18_177179.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_177179 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 177179) < 262144 * m + 177179 := by
  apply descent_of_endpoint
  · rw [data_18_177179.1]; exact data_18_177179.2.2
  · rw [data_18_177179.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 178671). -/
theorem data_18_178671 : oddCount 178671 18 = 11 ∧
    acceleratedOrbit 18 178671 = 120740 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_178671 : ∀ j : Fin 18,
    178671 ≤ acceleratedOrbit j.val 178671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_178671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 178671) = 177147 * m + 120740 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 178671
  rw [data_18_178671.1, data_18_178671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_178671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 178671) < 262144 * m + 178671 := by
  apply descent_of_endpoint
  · rw [data_18_178671.1]; exact data_18_178671.2.2
  · rw [data_18_178671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 178927). -/
theorem data_18_178927 : oddCount 178927 18 = 11 ∧
    acceleratedOrbit 18 178927 = 120913 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_178927 : ∀ j : Fin 18,
    178927 ≤ acceleratedOrbit j.val 178927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_178927 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 178927) = 177147 * m + 120913 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 178927
  rw [data_18_178927.1, data_18_178927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_178927 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 178927) < 262144 * m + 178927 := by
  apply descent_of_endpoint
  · rw [data_18_178927.1]; exact data_18_178927.2.2
  · rw [data_18_178927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 179439). -/
theorem data_18_179439 : oddCount 179439 18 = 11 ∧
    acceleratedOrbit 18 179439 = 121259 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_179439 : ∀ j : Fin 18,
    179439 ≤ acceleratedOrbit j.val 179439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_179439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179439) = 177147 * m + 121259 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 179439
  rw [data_18_179439.1, data_18_179439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_179439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179439) < 262144 * m + 179439 := by
  apply descent_of_endpoint
  · rw [data_18_179439.1]; exact data_18_179439.2.2
  · rw [data_18_179439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 179483). -/
theorem data_18_179483 : oddCount 179483 18 = 11 ∧
    acceleratedOrbit 18 179483 = 121289 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_179483 : ∀ j : Fin 18,
    179483 ≤ acceleratedOrbit j.val 179483 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_179483 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179483) = 177147 * m + 121289 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 179483
  rw [data_18_179483.1, data_18_179483.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_179483 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179483) < 262144 * m + 179483 := by
  apply descent_of_endpoint
  · rw [data_18_179483.1]; exact data_18_179483.2.2
  · rw [data_18_179483.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 179611). -/
theorem data_18_179611 : oddCount 179611 18 = 11 ∧
    acceleratedOrbit 18 179611 = 121376 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_179611 : ∀ j : Fin 18,
    179611 ≤ acceleratedOrbit j.val 179611 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_179611 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179611) = 177147 * m + 121376 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 179611
  rw [data_18_179611.1, data_18_179611.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_179611 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179611) < 262144 * m + 179611 := by
  apply descent_of_endpoint
  · rw [data_18_179611.1]; exact data_18_179611.2.2
  · rw [data_18_179611.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 179739). -/
theorem data_18_179739 : oddCount 179739 18 = 11 ∧
    acceleratedOrbit 18 179739 = 121462 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_179739 : ∀ j : Fin 18,
    179739 ≤ acceleratedOrbit j.val 179739 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_179739 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179739) = 177147 * m + 121462 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 179739
  rw [data_18_179739.1, data_18_179739.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_179739 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 179739) < 262144 * m + 179739 := by
  apply descent_of_endpoint
  · rw [data_18_179739.1]; exact data_18_179739.2.2
  · rw [data_18_179739.2.1]; decide

end Collatz.Research.FirstDescent.Batch183
