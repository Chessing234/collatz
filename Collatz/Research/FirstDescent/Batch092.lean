import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 92. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch092
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57759). -/
theorem data_16_57759 : oddCount 57759 16 = 10 ∧
    acceleratedOrbit 16 57759 = 52043 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57759 : ∀ j : Fin 16,
    57759 ≤ acceleratedOrbit j.val 57759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57759 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57759) = 59049 * m + 52043 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57759
  rw [data_16_57759.1, data_16_57759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57759 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57759) < 65536 * m + 57759 := by
  apply descent_of_endpoint
  · rw [data_16_57759.1]; exact data_16_57759.2.2
  · rw [data_16_57759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57839). -/
theorem data_16_57839 : oddCount 57839 16 = 10 ∧
    acceleratedOrbit 16 57839 = 52115 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57839 : ∀ j : Fin 16,
    57839 ≤ acceleratedOrbit j.val 57839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57839 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57839) = 59049 * m + 52115 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57839
  rw [data_16_57839.1, data_16_57839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57839 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57839) < 65536 * m + 57839 := by
  apply descent_of_endpoint
  · rw [data_16_57839.1]; exact data_16_57839.2.2
  · rw [data_16_57839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57947). -/
theorem data_16_57947 : oddCount 57947 16 = 10 ∧
    acceleratedOrbit 16 57947 = 52213 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57947 : ∀ j : Fin 16,
    57947 ≤ acceleratedOrbit j.val 57947 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57947 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57947) = 59049 * m + 52213 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57947
  rw [data_16_57947.1, data_16_57947.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57947 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57947) < 65536 * m + 57947 := by
  apply descent_of_endpoint
  · rw [data_16_57947.1]; exact data_16_57947.2.2
  · rw [data_16_57947.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 58175). -/
theorem data_16_58175 : oddCount 58175 16 = 10 ∧
    acceleratedOrbit 16 58175 = 52418 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_58175 : ∀ j : Fin 16,
    58175 ≤ acceleratedOrbit j.val 58175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_58175 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58175) = 59049 * m + 52418 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 58175
  rw [data_16_58175.1, data_16_58175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_58175 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58175) < 65536 * m + 58175 := by
  apply descent_of_endpoint
  · rw [data_16_58175.1]; exact data_16_58175.2.2
  · rw [data_16_58175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 58203). -/
theorem data_16_58203 : oddCount 58203 16 = 10 ∧
    acceleratedOrbit 16 58203 = 52444 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_58203 : ∀ j : Fin 16,
    58203 ≤ acceleratedOrbit j.val 58203 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_58203 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58203) = 59049 * m + 52444 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 58203
  rw [data_16_58203.1, data_16_58203.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_58203 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58203) < 65536 * m + 58203 := by
  apply descent_of_endpoint
  · rw [data_16_58203.1]; exact data_16_58203.2.2
  · rw [data_16_58203.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 58495). -/
theorem data_16_58495 : oddCount 58495 16 = 10 ∧
    acceleratedOrbit 16 58495 = 52706 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_58495 : ∀ j : Fin 16,
    58495 ≤ acceleratedOrbit j.val 58495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_58495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58495) = 59049 * m + 52706 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 58495
  rw [data_16_58495.1, data_16_58495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_58495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58495) < 65536 * m + 58495 := by
  apply descent_of_endpoint
  · rw [data_16_58495.1]; exact data_16_58495.2.2
  · rw [data_16_58495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 58523). -/
theorem data_16_58523 : oddCount 58523 16 = 10 ∧
    acceleratedOrbit 16 58523 = 52732 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_58523 : ∀ j : Fin 16,
    58523 ≤ acceleratedOrbit j.val 58523 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_58523 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58523) = 59049 * m + 52732 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 58523
  rw [data_16_58523.1, data_16_58523.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_58523 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58523) < 65536 * m + 58523 := by
  apply descent_of_endpoint
  · rw [data_16_58523.1]; exact data_16_58523.2.2
  · rw [data_16_58523.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 58527). -/
theorem data_16_58527 : oddCount 58527 16 = 10 ∧
    acceleratedOrbit 16 58527 = 52735 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_58527 : ∀ j : Fin 16,
    58527 ≤ acceleratedOrbit j.val 58527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_58527 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58527) = 59049 * m + 52735 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 58527
  rw [data_16_58527.1, data_16_58527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_58527 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58527) < 65536 * m + 58527 := by
  apply descent_of_endpoint
  · rw [data_16_58527.1]; exact data_16_58527.2.2
  · rw [data_16_58527.2.1]; decide

end Collatz.Research.FirstDescent.Batch092
