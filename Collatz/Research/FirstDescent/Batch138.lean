import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 138. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch138
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 78695). -/
theorem data_18_78695 : oddCount 78695 18 = 11 ∧
    acceleratedOrbit 18 78695 = 53180 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_78695 : ∀ j : Fin 18,
    78695 ≤ acceleratedOrbit j.val 78695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_78695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 78695) = 177147 * m + 53180 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 78695
  rw [data_18_78695.1, data_18_78695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_78695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 78695) < 262144 * m + 78695 := by
  apply descent_of_endpoint
  · rw [data_18_78695.1]; exact data_18_78695.2.2
  · rw [data_18_78695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 79719). -/
theorem data_18_79719 : oddCount 79719 18 = 11 ∧
    acceleratedOrbit 18 79719 = 53872 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_79719 : ∀ j : Fin 18,
    79719 ≤ acceleratedOrbit j.val 79719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_79719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 79719) = 177147 * m + 53872 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 79719
  rw [data_18_79719.1, data_18_79719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_79719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 79719) < 262144 * m + 79719 := by
  apply descent_of_endpoint
  · rw [data_18_79719.1]; exact data_18_79719.2.2
  · rw [data_18_79719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 80155). -/
theorem data_18_80155 : oddCount 80155 18 = 11 ∧
    acceleratedOrbit 18 80155 = 54167 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_80155 : ∀ j : Fin 18,
    80155 ≤ acceleratedOrbit j.val 80155 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_80155 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80155) = 177147 * m + 54167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 80155
  rw [data_18_80155.1, data_18_80155.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_80155 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80155) < 262144 * m + 80155 := by
  apply descent_of_endpoint
  · rw [data_18_80155.1]; exact data_18_80155.2.2
  · rw [data_18_80155.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 80191). -/
theorem data_18_80191 : oddCount 80191 18 = 11 ∧
    acceleratedOrbit 18 80191 = 54191 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_80191 : ∀ j : Fin 18,
    80191 ≤ acceleratedOrbit j.val 80191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_80191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80191) = 177147 * m + 54191 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 80191
  rw [data_18_80191.1, data_18_80191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_80191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80191) < 262144 * m + 80191 := by
  apply descent_of_endpoint
  · rw [data_18_80191.1]; exact data_18_80191.2.2
  · rw [data_18_80191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 80923). -/
theorem data_18_80923 : oddCount 80923 18 = 11 ∧
    acceleratedOrbit 18 80923 = 54686 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_80923 : ∀ j : Fin 18,
    80923 ≤ acceleratedOrbit j.val 80923 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_80923 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80923) = 177147 * m + 54686 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 80923
  rw [data_18_80923.1, data_18_80923.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_80923 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80923) < 262144 * m + 80923 := by
  apply descent_of_endpoint
  · rw [data_18_80923.1]; exact data_18_80923.2.2
  · rw [data_18_80923.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 80999). -/
theorem data_18_80999 : oddCount 80999 18 = 11 ∧
    acceleratedOrbit 18 80999 = 54737 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_80999 : ∀ j : Fin 18,
    80999 ≤ acceleratedOrbit j.val 80999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_80999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80999) = 177147 * m + 54737 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 80999
  rw [data_18_80999.1, data_18_80999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_80999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 80999) < 262144 * m + 80999 := by
  apply descent_of_endpoint
  · rw [data_18_80999.1]; exact data_18_80999.2.2
  · rw [data_18_80999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 81215). -/
theorem data_18_81215 : oddCount 81215 18 = 11 ∧
    acceleratedOrbit 18 81215 = 54883 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_81215 : ∀ j : Fin 18,
    81215 ≤ acceleratedOrbit j.val 81215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_81215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 81215) = 177147 * m + 54883 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 81215
  rw [data_18_81215.1, data_18_81215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_81215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 81215) < 262144 * m + 81215 := by
  apply descent_of_endpoint
  · rw [data_18_81215.1]; exact data_18_81215.2.2
  · rw [data_18_81215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 81255). -/
theorem data_18_81255 : oddCount 81255 18 = 11 ∧
    acceleratedOrbit 18 81255 = 54910 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_81255 : ∀ j : Fin 18,
    81255 ≤ acceleratedOrbit j.val 81255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_81255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 81255) = 177147 * m + 54910 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 81255
  rw [data_18_81255.1, data_18_81255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_81255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 81255) < 262144 * m + 81255 := by
  apply descent_of_endpoint
  · rw [data_18_81255.1]; exact data_18_81255.2.2
  · rw [data_18_81255.2.1]; decide

end Collatz.Research.FirstDescent.Batch138
