import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 189. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch189
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 192991). -/
theorem data_18_192991 : oddCount 192991 18 = 11 ∧
    acceleratedOrbit 18 192991 = 130417 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_192991 : ∀ j : Fin 18,
    192991 ≤ acceleratedOrbit j.val 192991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_192991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 192991) = 177147 * m + 130417 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 192991
  rw [data_18_192991.1, data_18_192991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_192991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 192991) < 262144 * m + 192991 := by
  apply descent_of_endpoint
  · rw [data_18_192991.1]; exact data_18_192991.2.2
  · rw [data_18_192991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 193627). -/
theorem data_18_193627 : oddCount 193627 18 = 11 ∧
    acceleratedOrbit 18 193627 = 130847 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_193627 : ∀ j : Fin 18,
    193627 ≤ acceleratedOrbit j.val 193627 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_193627 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 193627) = 177147 * m + 130847 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 193627
  rw [data_18_193627.1, data_18_193627.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_193627 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 193627) < 262144 * m + 193627 := by
  apply descent_of_endpoint
  · rw [data_18_193627.1]; exact data_18_193627.2.2
  · rw [data_18_193627.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 193663). -/
theorem data_18_193663 : oddCount 193663 18 = 11 ∧
    acceleratedOrbit 18 193663 = 130871 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_193663 : ∀ j : Fin 18,
    193663 ≤ acceleratedOrbit j.val 193663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_193663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 193663) = 177147 * m + 130871 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 193663
  rw [data_18_193663.1, data_18_193663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_193663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 193663) < 262144 * m + 193663 := by
  apply descent_of_endpoint
  · rw [data_18_193663.1]; exact data_18_193663.2.2
  · rw [data_18_193663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 194075). -/
theorem data_18_194075 : oddCount 194075 18 = 11 ∧
    acceleratedOrbit 18 194075 = 131150 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_194075 : ∀ j : Fin 18,
    194075 ≤ acceleratedOrbit j.val 194075 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_194075 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 194075) = 177147 * m + 131150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 194075
  rw [data_18_194075.1, data_18_194075.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_194075 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 194075) < 262144 * m + 194075 := by
  apply descent_of_endpoint
  · rw [data_18_194075.1]; exact data_18_194075.2.2
  · rw [data_18_194075.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 194687). -/
theorem data_18_194687 : oddCount 194687 18 = 11 ∧
    acceleratedOrbit 18 194687 = 131563 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_194687 : ∀ j : Fin 18,
    194687 ≤ acceleratedOrbit j.val 194687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_194687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 194687) = 177147 * m + 131563 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 194687
  rw [data_18_194687.1, data_18_194687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_194687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 194687) < 262144 * m + 194687 := by
  apply descent_of_endpoint
  · rw [data_18_194687.1]; exact data_18_194687.2.2
  · rw [data_18_194687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 194919). -/
theorem data_18_194919 : oddCount 194919 18 = 11 ∧
    acceleratedOrbit 18 194919 = 131720 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_194919 : ∀ j : Fin 18,
    194919 ≤ acceleratedOrbit j.val 194919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_194919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 194919) = 177147 * m + 131720 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 194919
  rw [data_18_194919.1, data_18_194919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_194919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 194919) < 262144 * m + 194919 := by
  apply descent_of_endpoint
  · rw [data_18_194919.1]; exact data_18_194919.2.2
  · rw [data_18_194919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 195039). -/
theorem data_18_195039 : oddCount 195039 18 = 11 ∧
    acceleratedOrbit 18 195039 = 131801 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_195039 : ∀ j : Fin 18,
    195039 ≤ acceleratedOrbit j.val 195039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_195039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 195039) = 177147 * m + 131801 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 195039
  rw [data_18_195039.1, data_18_195039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_195039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 195039) < 262144 * m + 195039 := by
  apply descent_of_endpoint
  · rw [data_18_195039.1]; exact data_18_195039.2.2
  · rw [data_18_195039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 195199). -/
theorem data_18_195199 : oddCount 195199 18 = 11 ∧
    acceleratedOrbit 18 195199 = 131909 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_195199 : ∀ j : Fin 18,
    195199 ≤ acceleratedOrbit j.val 195199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_195199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 195199) = 177147 * m + 131909 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 195199
  rw [data_18_195199.1, data_18_195199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_195199 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 195199) < 262144 * m + 195199 := by
  apply descent_of_endpoint
  · rw [data_18_195199.1]; exact data_18_195199.2.2
  · rw [data_18_195199.2.1]; decide

end Collatz.Research.FirstDescent.Batch189
