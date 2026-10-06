import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 43. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch043
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 3535). -/
theorem data_16_3535 : oddCount 3535 16 = 10 ∧
    acceleratedOrbit 16 3535 = 3187 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_3535 : ∀ j : Fin 16,
    3535 ≤ acceleratedOrbit j.val 3535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_3535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3535) = 59049 * m + 3187 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 3535
  rw [data_16_3535.1, data_16_3535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_3535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3535) < 65536 * m + 3535 := by
  apply descent_of_endpoint
  · rw [data_16_3535.1]; exact data_16_3535.2.2
  · rw [data_16_3535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 3695). -/
theorem data_16_3695 : oddCount 3695 16 = 10 ∧
    acceleratedOrbit 16 3695 = 3331 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_3695 : ∀ j : Fin 16,
    3695 ≤ acceleratedOrbit j.val 3695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_3695 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3695) = 59049 * m + 3331 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 3695
  rw [data_16_3695.1, data_16_3695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_3695 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3695) < 65536 * m + 3695 := by
  apply descent_of_endpoint
  · rw [data_16_3695.1]; exact data_16_3695.2.2
  · rw [data_16_3695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 3815). -/
theorem data_16_3815 : oddCount 3815 16 = 10 ∧
    acceleratedOrbit 16 3815 = 3439 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_3815 : ∀ j : Fin 16,
    3815 ≤ acceleratedOrbit j.val 3815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_3815 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3815) = 59049 * m + 3439 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 3815
  rw [data_16_3815.1, data_16_3815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_3815 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3815) < 65536 * m + 3815 := by
  apply descent_of_endpoint
  · rw [data_16_3815.1]; exact data_16_3815.2.2
  · rw [data_16_3815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4319). -/
theorem data_16_4319 : oddCount 4319 16 = 10 ∧
    acceleratedOrbit 16 4319 = 3893 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4319 : ∀ j : Fin 16,
    4319 ≤ acceleratedOrbit j.val 4319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4319) = 59049 * m + 3893 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4319
  rw [data_16_4319.1, data_16_4319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4319) < 65536 * m + 4319 := by
  apply descent_of_endpoint
  · rw [data_16_4319.1]; exact data_16_4319.2.2
  · rw [data_16_4319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4335). -/
theorem data_16_4335 : oddCount 4335 16 = 10 ∧
    acceleratedOrbit 16 4335 = 3907 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4335 : ∀ j : Fin 16,
    4335 ≤ acceleratedOrbit j.val 4335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4335) = 59049 * m + 3907 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4335
  rw [data_16_4335.1, data_16_4335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4335) < 65536 * m + 4335 := by
  apply descent_of_endpoint
  · rw [data_16_4335.1]; exact data_16_4335.2.2
  · rw [data_16_4335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4379). -/
theorem data_16_4379 : oddCount 4379 16 = 10 ∧
    acceleratedOrbit 16 4379 = 3947 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4379 : ∀ j : Fin 16,
    4379 ≤ acceleratedOrbit j.val 4379 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4379 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4379) = 59049 * m + 3947 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4379
  rw [data_16_4379.1, data_16_4379.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4379 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4379) < 65536 * m + 4379 := by
  apply descent_of_endpoint
  · rw [data_16_4379.1]; exact data_16_4379.2.2
  · rw [data_16_4379.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4635). -/
theorem data_16_4635 : oddCount 4635 16 = 10 ∧
    acceleratedOrbit 16 4635 = 4178 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4635 : ∀ j : Fin 16,
    4635 ≤ acceleratedOrbit j.val 4635 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4635 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4635) = 59049 * m + 4178 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4635
  rw [data_16_4635.1, data_16_4635.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4635 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4635) < 65536 * m + 4635 := by
  apply descent_of_endpoint
  · rw [data_16_4635.1]; exact data_16_4635.2.2
  · rw [data_16_4635.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4775). -/
theorem data_16_4775 : oddCount 4775 16 = 10 ∧
    acceleratedOrbit 16 4775 = 4304 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4775 : ∀ j : Fin 16,
    4775 ≤ acceleratedOrbit j.val 4775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4775) = 59049 * m + 4304 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4775
  rw [data_16_4775.1, data_16_4775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4775) < 65536 * m + 4775 := by
  apply descent_of_endpoint
  · rw [data_16_4775.1]; exact data_16_4775.2.2
  · rw [data_16_4775.2.1]; decide

end Collatz.Research.FirstDescent.Batch043
