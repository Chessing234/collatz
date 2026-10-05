import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 257. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch257
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 105883). -/
theorem data_20_105883 : oddCount 105883 20 = 12 ∧
    acceleratedOrbit 20 105883 = 53665 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_105883 : ∀ j : Fin 20,
    105883 ≤ acceleratedOrbit j.val 105883 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_105883 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 105883) = 531441 * m + 53665 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 105883
  rw [data_20_105883.1, data_20_105883.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_105883 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 105883) < 1048576 * m + 105883 := by
  apply descent_of_endpoint
  · rw [data_20_105883.1]; exact data_20_105883.2.2
  · rw [data_20_105883.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 106111). -/
theorem data_20_106111 : oddCount 106111 20 = 12 ∧
    acceleratedOrbit 20 106111 = 53780 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_106111 : ∀ j : Fin 20,
    106111 ≤ acceleratedOrbit j.val 106111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_106111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 106111) = 531441 * m + 53780 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 106111
  rw [data_20_106111.1, data_20_106111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_106111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 106111) < 1048576 * m + 106111 := by
  apply descent_of_endpoint
  · rw [data_20_106111.1]; exact data_20_106111.2.2
  · rw [data_20_106111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 106523). -/
theorem data_20_106523 : oddCount 106523 20 = 12 ∧
    acceleratedOrbit 20 106523 = 53989 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_106523 : ∀ j : Fin 20,
    106523 ≤ acceleratedOrbit j.val 106523 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_106523 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 106523) = 531441 * m + 53989 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 106523
  rw [data_20_106523.1, data_20_106523.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_106523 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 106523) < 1048576 * m + 106523 := by
  apply descent_of_endpoint
  · rw [data_20_106523.1]; exact data_20_106523.2.2
  · rw [data_20_106523.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 107135). -/
theorem data_20_107135 : oddCount 107135 20 = 12 ∧
    acceleratedOrbit 20 107135 = 54299 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_107135 : ∀ j : Fin 20,
    107135 ≤ acceleratedOrbit j.val 107135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_107135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 107135) = 531441 * m + 54299 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 107135
  rw [data_20_107135.1, data_20_107135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_107135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 107135) < 1048576 * m + 107135 := by
  apply descent_of_endpoint
  · rw [data_20_107135.1]; exact data_20_107135.2.2
  · rw [data_20_107135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 107999). -/
theorem data_20_107999 : oddCount 107999 20 = 12 ∧
    acceleratedOrbit 20 107999 = 54737 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_107999 : ∀ j : Fin 20,
    107999 ≤ acceleratedOrbit j.val 107999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_107999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 107999) = 531441 * m + 54737 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 107999
  rw [data_20_107999.1, data_20_107999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_107999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 107999) < 1048576 * m + 107999 := by
  apply descent_of_endpoint
  · rw [data_20_107999.1]; exact data_20_107999.2.2
  · rw [data_20_107999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 108135). -/
theorem data_20_108135 : oddCount 108135 20 = 12 ∧
    acceleratedOrbit 20 108135 = 54806 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_108135 : ∀ j : Fin 20,
    108135 ≤ acceleratedOrbit j.val 108135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_108135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 108135) = 531441 * m + 54806 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 108135
  rw [data_20_108135.1, data_20_108135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_108135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 108135) < 1048576 * m + 108135 := by
  apply descent_of_endpoint
  · rw [data_20_108135.1]; exact data_20_108135.2.2
  · rw [data_20_108135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 108271). -/
theorem data_20_108271 : oddCount 108271 20 = 12 ∧
    acceleratedOrbit 20 108271 = 54875 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_108271 : ∀ j : Fin 20,
    108271 ≤ acceleratedOrbit j.val 108271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_108271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 108271) = 531441 * m + 54875 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 108271
  rw [data_20_108271.1, data_20_108271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_108271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 108271) < 1048576 * m + 108271 := by
  apply descent_of_endpoint
  · rw [data_20_108271.1]; exact data_20_108271.2.2
  · rw [data_20_108271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 108863). -/
theorem data_20_108863 : oddCount 108863 20 = 12 ∧
    acceleratedOrbit 20 108863 = 55175 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_108863 : ∀ j : Fin 20,
    108863 ≤ acceleratedOrbit j.val 108863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_108863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 108863) = 531441 * m + 55175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 108863
  rw [data_20_108863.1, data_20_108863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_108863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 108863) < 1048576 * m + 108863 := by
  apply descent_of_endpoint
  · rw [data_20_108863.1]; exact data_20_108863.2.2
  · rw [data_20_108863.2.1]; decide

end Collatz.Research.FirstDescent.Batch257
