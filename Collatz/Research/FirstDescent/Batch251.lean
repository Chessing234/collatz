import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 251. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch251
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 86695). -/
theorem data_20_86695 : oddCount 86695 20 = 12 ∧
    acceleratedOrbit 20 86695 = 43940 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_86695 : ∀ j : Fin 20,
    86695 ≤ acceleratedOrbit j.val 86695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_86695 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 86695) = 531441 * m + 43940 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 86695
  rw [data_20_86695.1, data_20_86695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_86695 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 86695) < 1048576 * m + 86695 := by
  apply descent_of_endpoint
  · rw [data_20_86695.1]; exact data_20_86695.2.2
  · rw [data_20_86695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 87199). -/
theorem data_20_87199 : oddCount 87199 20 = 12 ∧
    acceleratedOrbit 20 87199 = 44195 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_87199 : ∀ j : Fin 20,
    87199 ≤ acceleratedOrbit j.val 87199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_87199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 87199) = 531441 * m + 44195 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 87199
  rw [data_20_87199.1, data_20_87199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_87199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 87199) < 1048576 * m + 87199 := by
  apply descent_of_endpoint
  · rw [data_20_87199.1]; exact data_20_87199.2.2
  · rw [data_20_87199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 87323). -/
theorem data_20_87323 : oddCount 87323 20 = 12 ∧
    acceleratedOrbit 20 87323 = 44258 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_87323 : ∀ j : Fin 20,
    87323 ≤ acceleratedOrbit j.val 87323 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_87323 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 87323) = 531441 * m + 44258 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 87323
  rw [data_20_87323.1, data_20_87323.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_87323 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 87323) < 1048576 * m + 87323 := by
  apply descent_of_endpoint
  · rw [data_20_87323.1]; exact data_20_87323.2.2
  · rw [data_20_87323.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 88175). -/
theorem data_20_88175 : oddCount 88175 20 = 12 ∧
    acceleratedOrbit 20 88175 = 44690 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_88175 : ∀ j : Fin 20,
    88175 ≤ acceleratedOrbit j.val 88175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_88175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 88175) = 531441 * m + 44690 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 88175
  rw [data_20_88175.1, data_20_88175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_88175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 88175) < 1048576 * m + 88175 := by
  apply descent_of_endpoint
  · rw [data_20_88175.1]; exact data_20_88175.2.2
  · rw [data_20_88175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 88623). -/
theorem data_20_88623 : oddCount 88623 20 = 12 ∧
    acceleratedOrbit 20 88623 = 44917 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_88623 : ∀ j : Fin 20,
    88623 ≤ acceleratedOrbit j.val 88623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_88623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 88623) = 531441 * m + 44917 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 88623
  rw [data_20_88623.1, data_20_88623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_88623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 88623) < 1048576 * m + 88623 := by
  apply descent_of_endpoint
  · rw [data_20_88623.1]; exact data_20_88623.2.2
  · rw [data_20_88623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 88783). -/
theorem data_20_88783 : oddCount 88783 20 = 12 ∧
    acceleratedOrbit 20 88783 = 44998 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_88783 : ∀ j : Fin 20,
    88783 ≤ acceleratedOrbit j.val 88783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_88783 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 88783) = 531441 * m + 44998 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 88783
  rw [data_20_88783.1, data_20_88783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_88783 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 88783) < 1048576 * m + 88783 := by
  apply descent_of_endpoint
  · rw [data_20_88783.1]; exact data_20_88783.2.2
  · rw [data_20_88783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 89055). -/
theorem data_20_89055 : oddCount 89055 20 = 12 ∧
    acceleratedOrbit 20 89055 = 45136 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_89055 : ∀ j : Fin 20,
    89055 ≤ acceleratedOrbit j.val 89055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_89055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 89055) = 531441 * m + 45136 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 89055
  rw [data_20_89055.1, data_20_89055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_89055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 89055) < 1048576 * m + 89055 := by
  apply descent_of_endpoint
  · rw [data_20_89055.1]; exact data_20_89055.2.2
  · rw [data_20_89055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 90271). -/
theorem data_20_90271 : oddCount 90271 20 = 12 ∧
    acceleratedOrbit 20 90271 = 45752 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_90271 : ∀ j : Fin 20,
    90271 ≤ acceleratedOrbit j.val 90271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_90271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90271) = 531441 * m + 45752 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 90271
  rw [data_20_90271.1, data_20_90271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_90271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 90271) < 1048576 * m + 90271 := by
  apply descent_of_endpoint
  · rw [data_20_90271.1]; exact data_20_90271.2.2
  · rw [data_20_90271.2.1]; decide

end Collatz.Research.FirstDescent.Batch251
