import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 122. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch122
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 49199). -/
theorem data_18_49199 : oddCount 49199 18 = 11 ∧
    acceleratedOrbit 18 49199 = 33248 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_49199 : ∀ j : Fin 18,
    49199 ≤ acceleratedOrbit j.val 49199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_49199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49199) = 177147 * m + 33248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 49199
  rw [data_18_49199.1, data_18_49199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_49199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49199) < 262144 * m + 49199 := by
  apply descent_of_endpoint
  · rw [data_18_49199.1]; exact data_18_49199.2.2
  · rw [data_18_49199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 49279). -/
theorem data_18_49279 : oddCount 49279 18 = 11 ∧
    acceleratedOrbit 18 49279 = 33302 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_49279 : ∀ j : Fin 18,
    49279 ≤ acceleratedOrbit j.val 49279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_49279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49279) = 177147 * m + 33302 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 49279
  rw [data_18_49279.1, data_18_49279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_49279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49279) < 262144 * m + 49279 := by
  apply descent_of_endpoint
  · rw [data_18_49279.1]; exact data_18_49279.2.2
  · rw [data_18_49279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 49403). -/
theorem data_18_49403 : oddCount 49403 18 = 11 ∧
    acceleratedOrbit 18 49403 = 33386 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_49403 : ∀ j : Fin 18,
    49403 ≤ acceleratedOrbit j.val 49403 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_49403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49403) = 177147 * m + 33386 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 49403
  rw [data_18_49403.1, data_18_49403.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_49403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49403) < 262144 * m + 49403 := by
  apply descent_of_endpoint
  · rw [data_18_49403.1]; exact data_18_49403.2.2
  · rw [data_18_49403.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 49599). -/
theorem data_18_49599 : oddCount 49599 18 = 11 ∧
    acceleratedOrbit 18 49599 = 33518 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_49599 : ∀ j : Fin 18,
    49599 ≤ acceleratedOrbit j.val 49599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_49599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49599) = 177147 * m + 33518 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 49599
  rw [data_18_49599.1, data_18_49599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_49599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 49599) < 262144 * m + 49599 := by
  apply descent_of_endpoint
  · rw [data_18_49599.1]; exact data_18_49599.2.2
  · rw [data_18_49599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 50895). -/
theorem data_18_50895 : oddCount 50895 18 = 11 ∧
    acceleratedOrbit 18 50895 = 34394 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_50895 : ∀ j : Fin 18,
    50895 ≤ acceleratedOrbit j.val 50895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_50895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 50895) = 177147 * m + 34394 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 50895
  rw [data_18_50895.1, data_18_50895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_50895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 50895) < 262144 * m + 50895 := by
  apply descent_of_endpoint
  · rw [data_18_50895.1]; exact data_18_50895.2.2
  · rw [data_18_50895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 51035). -/
theorem data_18_51035 : oddCount 51035 18 = 11 ∧
    acceleratedOrbit 18 51035 = 34489 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_51035 : ∀ j : Fin 18,
    51035 ≤ acceleratedOrbit j.val 51035 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_51035 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51035) = 177147 * m + 34489 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 51035
  rw [data_18_51035.1, data_18_51035.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_51035 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51035) < 262144 * m + 51035 := by
  apply descent_of_endpoint
  · rw [data_18_51035.1]; exact data_18_51035.2.2
  · rw [data_18_51035.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 51311). -/
theorem data_18_51311 : oddCount 51311 18 = 11 ∧
    acceleratedOrbit 18 51311 = 34675 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_51311 : ∀ j : Fin 18,
    51311 ≤ acceleratedOrbit j.val 51311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_51311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51311) = 177147 * m + 34675 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 51311
  rw [data_18_51311.1, data_18_51311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_51311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51311) < 262144 * m + 51311 := by
  apply descent_of_endpoint
  · rw [data_18_51311.1]; exact data_18_51311.2.2
  · rw [data_18_51311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 51867). -/
theorem data_18_51867 : oddCount 51867 18 = 11 ∧
    acceleratedOrbit 18 51867 = 35051 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_51867 : ∀ j : Fin 18,
    51867 ≤ acceleratedOrbit j.val 51867 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_51867 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51867) = 177147 * m + 35051 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 51867
  rw [data_18_51867.1, data_18_51867.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_51867 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51867) < 262144 * m + 51867 := by
  apply descent_of_endpoint
  · rw [data_18_51867.1]; exact data_18_51867.2.2
  · rw [data_18_51867.2.1]; decide

end Collatz.Research.FirstDescent.Batch122
