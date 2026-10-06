import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 281. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch281
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 187007). -/
theorem data_20_187007 : oddCount 187007 20 = 12 ∧
    acceleratedOrbit 20 187007 = 94780 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_187007 : ∀ j : Fin 20,
    187007 ≤ acceleratedOrbit j.val 187007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_187007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187007) = 531441 * m + 94780 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 187007
  rw [data_20_187007.1, data_20_187007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_187007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187007) < 1048576 * m + 187007 := by
  apply descent_of_endpoint
  · rw [data_20_187007.1]; exact data_20_187007.2.2
  · rw [data_20_187007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 187163). -/
theorem data_20_187163 : oddCount 187163 20 = 12 ∧
    acceleratedOrbit 20 187163 = 94859 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_187163 : ∀ j : Fin 20,
    187163 ≤ acceleratedOrbit j.val 187163 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_187163 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187163) = 531441 * m + 94859 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 187163
  rw [data_20_187163.1, data_20_187163.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_187163 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187163) < 1048576 * m + 187163 := by
  apply descent_of_endpoint
  · rw [data_20_187163.1]; exact data_20_187163.2.2
  · rw [data_20_187163.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 187423). -/
theorem data_20_187423 : oddCount 187423 20 = 12 ∧
    acceleratedOrbit 20 187423 = 94991 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_187423 : ∀ j : Fin 20,
    187423 ≤ acceleratedOrbit j.val 187423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_187423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187423) = 531441 * m + 94991 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 187423
  rw [data_20_187423.1, data_20_187423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_187423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187423) < 1048576 * m + 187423 := by
  apply descent_of_endpoint
  · rw [data_20_187423.1]; exact data_20_187423.2.2
  · rw [data_20_187423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 187547). -/
theorem data_20_187547 : oddCount 187547 20 = 12 ∧
    acceleratedOrbit 20 187547 = 95054 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_187547 : ∀ j : Fin 20,
    187547 ≤ acceleratedOrbit j.val 187547 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_187547 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187547) = 531441 * m + 95054 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 187547
  rw [data_20_187547.1, data_20_187547.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_187547 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187547) < 1048576 * m + 187547 := by
  apply descent_of_endpoint
  · rw [data_20_187547.1]; exact data_20_187547.2.2
  · rw [data_20_187547.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 187583). -/
theorem data_20_187583 : oddCount 187583 20 = 12 ∧
    acceleratedOrbit 20 187583 = 95072 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_187583 : ∀ j : Fin 20,
    187583 ≤ acceleratedOrbit j.val 187583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_187583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187583) = 531441 * m + 95072 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 187583
  rw [data_20_187583.1, data_20_187583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_187583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187583) < 1048576 * m + 187583 := by
  apply descent_of_endpoint
  · rw [data_20_187583.1]; exact data_20_187583.2.2
  · rw [data_20_187583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 187871). -/
theorem data_20_187871 : oddCount 187871 20 = 12 ∧
    acceleratedOrbit 20 187871 = 95218 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_187871 : ∀ j : Fin 20,
    187871 ≤ acceleratedOrbit j.val 187871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_187871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187871) = 531441 * m + 95218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 187871
  rw [data_20_187871.1, data_20_187871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_187871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 187871) < 1048576 * m + 187871 := by
  apply descent_of_endpoint
  · rw [data_20_187871.1]; exact data_20_187871.2.2
  · rw [data_20_187871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 188187). -/
theorem data_20_188187 : oddCount 188187 20 = 12 ∧
    acceleratedOrbit 20 188187 = 95378 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_188187 : ∀ j : Fin 20,
    188187 ≤ acceleratedOrbit j.val 188187 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_188187 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 188187) = 531441 * m + 95378 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 188187
  rw [data_20_188187.1, data_20_188187.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_188187 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 188187) < 1048576 * m + 188187 := by
  apply descent_of_endpoint
  · rw [data_20_188187.1]; exact data_20_188187.2.2
  · rw [data_20_188187.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 188351). -/
theorem data_20_188351 : oddCount 188351 20 = 12 ∧
    acceleratedOrbit 20 188351 = 95461 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_188351 : ∀ j : Fin 20,
    188351 ≤ acceleratedOrbit j.val 188351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_188351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 188351) = 531441 * m + 95461 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 188351
  rw [data_20_188351.1, data_20_188351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_188351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 188351) < 1048576 * m + 188351 := by
  apply descent_of_endpoint
  · rw [data_20_188351.1]; exact data_20_188351.2.2
  · rw [data_20_188351.2.1]; decide

end Collatz.Research.FirstDescent.Batch281
