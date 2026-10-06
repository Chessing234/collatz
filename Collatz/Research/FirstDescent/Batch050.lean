import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 50. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch050
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 11823). -/
theorem data_16_11823 : oddCount 11823 16 = 10 ∧
    acceleratedOrbit 16 11823 = 10654 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_11823 : ∀ j : Fin 16,
    11823 ≤ acceleratedOrbit j.val 11823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_11823 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11823) = 59049 * m + 10654 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 11823
  rw [data_16_11823.1, data_16_11823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_11823 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11823) < 65536 * m + 11823 := by
  apply descent_of_endpoint
  · rw [data_16_11823.1]; exact data_16_11823.2.2
  · rw [data_16_11823.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 11887). -/
theorem data_16_11887 : oddCount 11887 16 = 10 ∧
    acceleratedOrbit 16 11887 = 10712 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_11887 : ∀ j : Fin 16,
    11887 ≤ acceleratedOrbit j.val 11887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_11887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11887) = 59049 * m + 10712 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 11887
  rw [data_16_11887.1, data_16_11887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_11887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11887) < 65536 * m + 11887 := by
  apply descent_of_endpoint
  · rw [data_16_11887.1]; exact data_16_11887.2.2
  · rw [data_16_11887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 12007). -/
theorem data_16_12007 : oddCount 12007 16 = 10 ∧
    acceleratedOrbit 16 12007 = 10820 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_12007 : ∀ j : Fin 16,
    12007 ≤ acceleratedOrbit j.val 12007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_12007 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12007) = 59049 * m + 10820 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 12007
  rw [data_16_12007.1, data_16_12007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_12007 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12007) < 65536 * m + 12007 := by
  apply descent_of_endpoint
  · rw [data_16_12007.1]; exact data_16_12007.2.2
  · rw [data_16_12007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 12319). -/
theorem data_16_12319 : oddCount 12319 16 = 10 ∧
    acceleratedOrbit 16 12319 = 11101 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_12319 : ∀ j : Fin 16,
    12319 ≤ acceleratedOrbit j.val 12319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_12319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12319) = 59049 * m + 11101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 12319
  rw [data_16_12319.1, data_16_12319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_12319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12319) < 65536 * m + 12319 := by
  apply descent_of_endpoint
  · rw [data_16_12319.1]; exact data_16_12319.2.2
  · rw [data_16_12319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 12495). -/
theorem data_16_12495 : oddCount 12495 16 = 10 ∧
    acceleratedOrbit 16 12495 = 11260 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_12495 : ∀ j : Fin 16,
    12495 ≤ acceleratedOrbit j.val 12495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_12495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12495) = 59049 * m + 11260 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 12495
  rw [data_16_12495.1, data_16_12495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_12495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12495) < 65536 * m + 12495 := by
  apply descent_of_endpoint
  · rw [data_16_12495.1]; exact data_16_12495.2.2
  · rw [data_16_12495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 12615). -/
theorem data_16_12615 : oddCount 12615 16 = 10 ∧
    acceleratedOrbit 16 12615 = 11368 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_12615 : ∀ j : Fin 16,
    12615 ≤ acceleratedOrbit j.val 12615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_12615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12615) = 59049 * m + 11368 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 12615
  rw [data_16_12615.1, data_16_12615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_12615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12615) < 65536 * m + 12615 := by
  apply descent_of_endpoint
  · rw [data_16_12615.1]; exact data_16_12615.2.2
  · rw [data_16_12615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 12775). -/
theorem data_16_12775 : oddCount 12775 16 = 10 ∧
    acceleratedOrbit 16 12775 = 11512 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_12775 : ∀ j : Fin 16,
    12775 ≤ acceleratedOrbit j.val 12775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_12775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12775) = 59049 * m + 11512 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 12775
  rw [data_16_12775.1, data_16_12775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_12775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12775) < 65536 * m + 12775 := by
  apply descent_of_endpoint
  · rw [data_16_12775.1]; exact data_16_12775.2.2
  · rw [data_16_12775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 12799). -/
theorem data_16_12799 : oddCount 12799 16 = 10 ∧
    acceleratedOrbit 16 12799 = 11533 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_12799 : ∀ j : Fin 16,
    12799 ≤ acceleratedOrbit j.val 12799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_12799 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12799) = 59049 * m + 11533 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 12799
  rw [data_16_12799.1, data_16_12799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_12799 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 12799) < 65536 * m + 12799 := by
  apply descent_of_endpoint
  · rw [data_16_12799.1]; exact data_16_12799.2.2
  · rw [data_16_12799.2.1]; decide

end Collatz.Research.FirstDescent.Batch050
