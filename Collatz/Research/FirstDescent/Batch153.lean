import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 153. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch153
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 111919). -/
theorem data_18_111919 : oddCount 111919 18 = 11 ∧
    acceleratedOrbit 18 111919 = 75632 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_111919 : ∀ j : Fin 18,
    111919 ≤ acceleratedOrbit j.val 111919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_111919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111919) = 177147 * m + 75632 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 111919
  rw [data_18_111919.1, data_18_111919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_111919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 111919) < 262144 * m + 111919 := by
  apply descent_of_endpoint
  · rw [data_18_111919.1]; exact data_18_111919.2.2
  · rw [data_18_111919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112079). -/
theorem data_18_112079 : oddCount 112079 18 = 11 ∧
    acceleratedOrbit 18 112079 = 75740 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112079 : ∀ j : Fin 18,
    112079 ≤ acceleratedOrbit j.val 112079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112079) = 177147 * m + 75740 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112079
  rw [data_18_112079.1, data_18_112079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112079) < 262144 * m + 112079 := by
  apply descent_of_endpoint
  · rw [data_18_112079.1]; exact data_18_112079.2.2
  · rw [data_18_112079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112127). -/
theorem data_18_112127 : oddCount 112127 18 = 11 ∧
    acceleratedOrbit 18 112127 = 75772 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112127 : ∀ j : Fin 18,
    112127 ≤ acceleratedOrbit j.val 112127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112127) = 177147 * m + 75772 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112127
  rw [data_18_112127.1, data_18_112127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112127) < 262144 * m + 112127 := by
  apply descent_of_endpoint
  · rw [data_18_112127.1]; exact data_18_112127.2.2
  · rw [data_18_112127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112159). -/
theorem data_18_112159 : oddCount 112159 18 = 11 ∧
    acceleratedOrbit 18 112159 = 75794 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112159 : ∀ j : Fin 18,
    112159 ≤ acceleratedOrbit j.val 112159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112159) = 177147 * m + 75794 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112159
  rw [data_18_112159.1, data_18_112159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112159) < 262144 * m + 112159 := by
  apply descent_of_endpoint
  · rw [data_18_112159.1]; exact data_18_112159.2.2
  · rw [data_18_112159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112319). -/
theorem data_18_112319 : oddCount 112319 18 = 11 ∧
    acceleratedOrbit 18 112319 = 75902 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112319 : ∀ j : Fin 18,
    112319 ≤ acceleratedOrbit j.val 112319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112319) = 177147 * m + 75902 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112319
  rw [data_18_112319.1, data_18_112319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112319) < 262144 * m + 112319 := by
  apply descent_of_endpoint
  · rw [data_18_112319.1]; exact data_18_112319.2.2
  · rw [data_18_112319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112359). -/
theorem data_18_112359 : oddCount 112359 18 = 11 ∧
    acceleratedOrbit 18 112359 = 75929 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112359 : ∀ j : Fin 18,
    112359 ≤ acceleratedOrbit j.val 112359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112359) = 177147 * m + 75929 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112359
  rw [data_18_112359.1, data_18_112359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112359) < 262144 * m + 112359 := by
  apply descent_of_endpoint
  · rw [data_18_112359.1]; exact data_18_112359.2.2
  · rw [data_18_112359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112495). -/
theorem data_18_112495 : oddCount 112495 18 = 11 ∧
    acceleratedOrbit 18 112495 = 76021 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112495 : ∀ j : Fin 18,
    112495 ≤ acceleratedOrbit j.val 112495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112495) = 177147 * m + 76021 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112495
  rw [data_18_112495.1, data_18_112495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112495) < 262144 * m + 112495 := by
  apply descent_of_endpoint
  · rw [data_18_112495.1]; exact data_18_112495.2.2
  · rw [data_18_112495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112607). -/
theorem data_18_112607 : oddCount 112607 18 = 11 ∧
    acceleratedOrbit 18 112607 = 76097 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112607 : ∀ j : Fin 18,
    112607 ≤ acceleratedOrbit j.val 112607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112607) = 177147 * m + 76097 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112607
  rw [data_18_112607.1, data_18_112607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112607) < 262144 * m + 112607 := by
  apply descent_of_endpoint
  · rw [data_18_112607.1]; exact data_18_112607.2.2
  · rw [data_18_112607.2.1]; decide

end Collatz.Research.FirstDescent.Batch153
