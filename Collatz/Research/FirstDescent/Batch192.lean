import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 192. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch192
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 201759). -/
theorem data_18_201759 : oddCount 201759 18 = 11 ∧
    acceleratedOrbit 18 201759 = 136342 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_201759 : ∀ j : Fin 18,
    201759 ≤ acceleratedOrbit j.val 201759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_201759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 201759) = 177147 * m + 136342 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 201759
  rw [data_18_201759.1, data_18_201759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_201759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 201759) < 262144 * m + 201759 := by
  apply descent_of_endpoint
  · rw [data_18_201759.1]; exact data_18_201759.2.2
  · rw [data_18_201759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 202111). -/
theorem data_18_202111 : oddCount 202111 18 = 11 ∧
    acceleratedOrbit 18 202111 = 136580 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_202111 : ∀ j : Fin 18,
    202111 ≤ acceleratedOrbit j.val 202111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_202111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 202111) = 177147 * m + 136580 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 202111
  rw [data_18_202111.1, data_18_202111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_202111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 202111) < 262144 * m + 202111 := by
  apply descent_of_endpoint
  · rw [data_18_202111.1]; exact data_18_202111.2.2
  · rw [data_18_202111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 202879). -/
theorem data_18_202879 : oddCount 202879 18 = 11 ∧
    acceleratedOrbit 18 202879 = 137099 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_202879 : ∀ j : Fin 18,
    202879 ≤ acceleratedOrbit j.val 202879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_202879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 202879) = 177147 * m + 137099 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 202879
  rw [data_18_202879.1, data_18_202879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_202879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 202879) < 262144 * m + 202879 := by
  apply descent_of_endpoint
  · rw [data_18_202879.1]; exact data_18_202879.2.2
  · rw [data_18_202879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 203003). -/
theorem data_18_203003 : oddCount 203003 18 = 11 ∧
    acceleratedOrbit 18 203003 = 137183 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_203003 : ∀ j : Fin 18,
    203003 ≤ acceleratedOrbit j.val 203003 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_203003 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 203003) = 177147 * m + 137183 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 203003
  rw [data_18_203003.1, data_18_203003.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_203003 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 203003) < 262144 * m + 203003 := by
  apply descent_of_endpoint
  · rw [data_18_203003.1]; exact data_18_203003.2.2
  · rw [data_18_203003.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 203419). -/
theorem data_18_203419 : oddCount 203419 18 = 11 ∧
    acceleratedOrbit 18 203419 = 137464 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_203419 : ∀ j : Fin 18,
    203419 ≤ acceleratedOrbit j.val 203419 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_203419 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 203419) = 177147 * m + 137464 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 203419
  rw [data_18_203419.1, data_18_203419.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_203419 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 203419) < 262144 * m + 203419 := by
  apply descent_of_endpoint
  · rw [data_18_203419.1]; exact data_18_203419.2.2
  · rw [data_18_203419.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 203743). -/
theorem data_18_203743 : oddCount 203743 18 = 11 ∧
    acceleratedOrbit 18 203743 = 137683 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_203743 : ∀ j : Fin 18,
    203743 ≤ acceleratedOrbit j.val 203743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_203743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 203743) = 177147 * m + 137683 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 203743
  rw [data_18_203743.1, data_18_203743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_203743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 203743) < 262144 * m + 203743 := by
  apply descent_of_endpoint
  · rw [data_18_203743.1]; exact data_18_203743.2.2
  · rw [data_18_203743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204255). -/
theorem data_18_204255 : oddCount 204255 18 = 11 ∧
    acceleratedOrbit 18 204255 = 138029 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204255 : ∀ j : Fin 18,
    204255 ≤ acceleratedOrbit j.val 204255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204255) = 177147 * m + 138029 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204255
  rw [data_18_204255.1, data_18_204255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204255) < 262144 * m + 204255 := by
  apply descent_of_endpoint
  · rw [data_18_204255.1]; exact data_18_204255.2.2
  · rw [data_18_204255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 204335). -/
theorem data_18_204335 : oddCount 204335 18 = 11 ∧
    acceleratedOrbit 18 204335 = 138083 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_204335 : ∀ j : Fin 18,
    204335 ≤ acceleratedOrbit j.val 204335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_204335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204335) = 177147 * m + 138083 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 204335
  rw [data_18_204335.1, data_18_204335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_204335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 204335) < 262144 * m + 204335 := by
  apply descent_of_endpoint
  · rw [data_18_204335.1]; exact data_18_204335.2.2
  · rw [data_18_204335.2.1]; decide

end Collatz.Research.FirstDescent.Batch192
