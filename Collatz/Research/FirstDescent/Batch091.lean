import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 91. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch091
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 56347). -/
theorem data_16_56347 : oddCount 56347 16 = 10 ∧
    acceleratedOrbit 16 56347 = 50771 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_56347 : ∀ j : Fin 16,
    56347 ≤ acceleratedOrbit j.val 56347 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_56347 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56347) = 59049 * m + 50771 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 56347
  rw [data_16_56347.1, data_16_56347.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_56347 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56347) < 65536 * m + 56347 := by
  apply descent_of_endpoint
  · rw [data_16_56347.1]; exact data_16_56347.2.2
  · rw [data_16_56347.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 56639). -/
theorem data_16_56639 : oddCount 56639 16 = 10 ∧
    acceleratedOrbit 16 56639 = 51034 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_56639 : ∀ j : Fin 16,
    56639 ≤ acceleratedOrbit j.val 56639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_56639 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56639) = 59049 * m + 51034 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 56639
  rw [data_16_56639.1, data_16_56639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_56639 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56639) < 65536 * m + 56639 := by
  apply descent_of_endpoint
  · rw [data_16_56639.1]; exact data_16_56639.2.2
  · rw [data_16_56639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 56935). -/
theorem data_16_56935 : oddCount 56935 16 = 10 ∧
    acceleratedOrbit 16 56935 = 51301 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_56935 : ∀ j : Fin 16,
    56935 ≤ acceleratedOrbit j.val 56935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_56935 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56935) = 59049 * m + 51301 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 56935
  rw [data_16_56935.1, data_16_56935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_56935 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56935) < 65536 * m + 56935 := by
  apply descent_of_endpoint
  · rw [data_16_56935.1]; exact data_16_56935.2.2
  · rw [data_16_56935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57179). -/
theorem data_16_57179 : oddCount 57179 16 = 10 ∧
    acceleratedOrbit 16 57179 = 51521 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57179 : ∀ j : Fin 16,
    57179 ≤ acceleratedOrbit j.val 57179 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57179 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57179) = 59049 * m + 51521 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57179
  rw [data_16_57179.1, data_16_57179.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57179 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57179) < 65536 * m + 57179 := by
  apply descent_of_endpoint
  · rw [data_16_57179.1]; exact data_16_57179.2.2
  · rw [data_16_57179.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57215). -/
theorem data_16_57215 : oddCount 57215 16 = 10 ∧
    acceleratedOrbit 16 57215 = 51553 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57215 : ∀ j : Fin 16,
    57215 ≤ acceleratedOrbit j.val 57215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57215) = 59049 * m + 51553 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57215
  rw [data_16_57215.1, data_16_57215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57215) < 65536 * m + 57215 := by
  apply descent_of_endpoint
  · rw [data_16_57215.1]; exact data_16_57215.2.2
  · rw [data_16_57215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57375). -/
theorem data_16_57375 : oddCount 57375 16 = 10 ∧
    acceleratedOrbit 16 57375 = 51697 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57375 : ∀ j : Fin 16,
    57375 ≤ acceleratedOrbit j.val 57375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57375) = 59049 * m + 51697 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57375
  rw [data_16_57375.1, data_16_57375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57375) < 65536 * m + 57375 := by
  apply descent_of_endpoint
  · rw [data_16_57375.1]; exact data_16_57375.2.2
  · rw [data_16_57375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57671). -/
theorem data_16_57671 : oddCount 57671 16 = 10 ∧
    acceleratedOrbit 16 57671 = 51964 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57671 : ∀ j : Fin 16,
    57671 ≤ acceleratedOrbit j.val 57671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57671) = 59049 * m + 51964 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57671
  rw [data_16_57671.1, data_16_57671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57671) < 65536 * m + 57671 := by
  apply descent_of_endpoint
  · rw [data_16_57671.1]; exact data_16_57671.2.2
  · rw [data_16_57671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 57755). -/
theorem data_16_57755 : oddCount 57755 16 = 10 ∧
    acceleratedOrbit 16 57755 = 52040 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_57755 : ∀ j : Fin 16,
    57755 ≤ acceleratedOrbit j.val 57755 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_57755 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57755) = 59049 * m + 52040 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 57755
  rw [data_16_57755.1, data_16_57755.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_57755 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 57755) < 65536 * m + 57755 := by
  apply descent_of_endpoint
  · rw [data_16_57755.1]; exact data_16_57755.2.2
  · rw [data_16_57755.2.1]; decide

end Collatz.Research.FirstDescent.Batch091
