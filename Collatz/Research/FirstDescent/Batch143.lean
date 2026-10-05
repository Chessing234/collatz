import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 143. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch143
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 91631). -/
theorem data_18_91631 : oddCount 91631 18 = 11 ∧
    acceleratedOrbit 18 91631 = 61922 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_91631 : ∀ j : Fin 18,
    91631 ≤ acceleratedOrbit j.val 91631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_91631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91631) = 177147 * m + 61922 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 91631
  rw [data_18_91631.1, data_18_91631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_91631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91631) < 262144 * m + 91631 := by
  apply descent_of_endpoint
  · rw [data_18_91631.1]; exact data_18_91631.2.2
  · rw [data_18_91631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 91751). -/
theorem data_18_91751 : oddCount 91751 18 = 11 ∧
    acceleratedOrbit 18 91751 = 62003 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_91751 : ∀ j : Fin 18,
    91751 ≤ acceleratedOrbit j.val 91751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_91751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91751) = 177147 * m + 62003 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 91751
  rw [data_18_91751.1, data_18_91751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_91751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 91751) < 262144 * m + 91751 := by
  apply descent_of_endpoint
  · rw [data_18_91751.1]; exact data_18_91751.2.2
  · rw [data_18_91751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 92031). -/
theorem data_18_92031 : oddCount 92031 18 = 11 ∧
    acceleratedOrbit 18 92031 = 62192 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_92031 : ∀ j : Fin 18,
    92031 ≤ acceleratedOrbit j.val 92031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_92031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 92031) = 177147 * m + 62192 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 92031
  rw [data_18_92031.1, data_18_92031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_92031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 92031) < 262144 * m + 92031 := by
  apply descent_of_endpoint
  · rw [data_18_92031.1]; exact data_18_92031.2.2
  · rw [data_18_92031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 93743). -/
theorem data_18_93743 : oddCount 93743 18 = 11 ∧
    acceleratedOrbit 18 93743 = 63349 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_93743 : ∀ j : Fin 18,
    93743 ≤ acceleratedOrbit j.val 93743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_93743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 93743) = 177147 * m + 63349 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 93743
  rw [data_18_93743.1, data_18_93743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_93743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 93743) < 262144 * m + 93743 := by
  apply descent_of_endpoint
  · rw [data_18_93743.1]; exact data_18_93743.2.2
  · rw [data_18_93743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 94299). -/
theorem data_18_94299 : oddCount 94299 18 = 11 ∧
    acceleratedOrbit 18 94299 = 63725 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_94299 : ∀ j : Fin 18,
    94299 ≤ acceleratedOrbit j.val 94299 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_94299 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 94299) = 177147 * m + 63725 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 94299
  rw [data_18_94299.1, data_18_94299.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_94299 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 94299) < 262144 * m + 94299 := by
  apply descent_of_endpoint
  · rw [data_18_94299.1]; exact data_18_94299.2.2
  · rw [data_18_94299.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 94747). -/
theorem data_18_94747 : oddCount 94747 18 = 11 ∧
    acceleratedOrbit 18 94747 = 64028 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_94747 : ∀ j : Fin 18,
    94747 ≤ acceleratedOrbit j.val 94747 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_94747 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 94747) = 177147 * m + 64028 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 94747
  rw [data_18_94747.1, data_18_94747.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_94747 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 94747) < 262144 * m + 94747 := by
  apply descent_of_endpoint
  · rw [data_18_94747.1]; exact data_18_94747.2.2
  · rw [data_18_94747.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 94875). -/
theorem data_18_94875 : oddCount 94875 18 = 11 ∧
    acceleratedOrbit 18 94875 = 64114 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_94875 : ∀ j : Fin 18,
    94875 ≤ acceleratedOrbit j.val 94875 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_94875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 94875) = 177147 * m + 64114 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 94875
  rw [data_18_94875.1, data_18_94875.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_94875 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 94875) < 262144 * m + 94875 := by
  apply descent_of_endpoint
  · rw [data_18_94875.1]; exact data_18_94875.2.2
  · rw [data_18_94875.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 95199). -/
theorem data_18_95199 : oddCount 95199 18 = 11 ∧
    acceleratedOrbit 18 95199 = 64333 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_95199 : ∀ j : Fin 18,
    95199 ≤ acceleratedOrbit j.val 95199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_95199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95199) = 177147 * m + 64333 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 95199
  rw [data_18_95199.1, data_18_95199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_95199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 95199) < 262144 * m + 95199 := by
  apply descent_of_endpoint
  · rw [data_18_95199.1]; exact data_18_95199.2.2
  · rw [data_18_95199.2.1]; decide

end Collatz.Research.FirstDescent.Batch143
