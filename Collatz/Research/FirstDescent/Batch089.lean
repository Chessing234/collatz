import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 89. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch089
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 54043). -/
theorem data_16_54043 : oddCount 54043 16 = 10 ∧
    acceleratedOrbit 16 54043 = 48695 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_54043 : ∀ j : Fin 16,
    54043 ≤ acceleratedOrbit j.val 54043 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_54043 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54043) = 59049 * m + 48695 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 54043
  rw [data_16_54043.1, data_16_54043.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_54043 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54043) < 65536 * m + 54043 := by
  apply descent_of_endpoint
  · rw [data_16_54043.1]; exact data_16_54043.2.2
  · rw [data_16_54043.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 54303). -/
theorem data_16_54303 : oddCount 54303 16 = 10 ∧
    acceleratedOrbit 16 54303 = 48929 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_54303 : ∀ j : Fin 16,
    54303 ≤ acceleratedOrbit j.val 54303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_54303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54303) = 59049 * m + 48929 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 54303
  rw [data_16_54303.1, data_16_54303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_54303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54303) < 65536 * m + 54303 := by
  apply descent_of_endpoint
  · rw [data_16_54303.1]; exact data_16_54303.2.2
  · rw [data_16_54303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 54319). -/
theorem data_16_54319 : oddCount 54319 16 = 10 ∧
    acceleratedOrbit 16 54319 = 48944 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_54319 : ∀ j : Fin 16,
    54319 ≤ acceleratedOrbit j.val 54319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_54319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54319) = 59049 * m + 48944 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 54319
  rw [data_16_54319.1, data_16_54319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_54319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54319) < 65536 * m + 54319 := by
  apply descent_of_endpoint
  · rw [data_16_54319.1]; exact data_16_54319.2.2
  · rw [data_16_54319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 54375). -/
theorem data_16_54375 : oddCount 54375 16 = 10 ∧
    acceleratedOrbit 16 54375 = 48994 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_54375 : ∀ j : Fin 16,
    54375 ≤ acceleratedOrbit j.val 54375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_54375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54375) = 59049 * m + 48994 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 54375
  rw [data_16_54375.1, data_16_54375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_54375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54375) < 65536 * m + 54375 := by
  apply descent_of_endpoint
  · rw [data_16_54375.1]; exact data_16_54375.2.2
  · rw [data_16_54375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 54439). -/
theorem data_16_54439 : oddCount 54439 16 = 10 ∧
    acceleratedOrbit 16 54439 = 49052 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_54439 : ∀ j : Fin 16,
    54439 ≤ acceleratedOrbit j.val 54439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_54439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54439) = 59049 * m + 49052 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 54439
  rw [data_16_54439.1, data_16_54439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_54439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54439) < 65536 * m + 54439 := by
  apply descent_of_endpoint
  · rw [data_16_54439.1]; exact data_16_54439.2.2
  · rw [data_16_54439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 54751). -/
theorem data_16_54751 : oddCount 54751 16 = 10 ∧
    acceleratedOrbit 16 54751 = 49333 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_54751 : ∀ j : Fin 16,
    54751 ≤ acceleratedOrbit j.val 54751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_54751 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54751) = 59049 * m + 49333 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 54751
  rw [data_16_54751.1, data_16_54751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_54751 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 54751) < 65536 * m + 54751 := by
  apply descent_of_endpoint
  · rw [data_16_54751.1]; exact data_16_54751.2.2
  · rw [data_16_54751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 55207). -/
theorem data_16_55207 : oddCount 55207 16 = 10 ∧
    acceleratedOrbit 16 55207 = 49744 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_55207 : ∀ j : Fin 16,
    55207 ≤ acceleratedOrbit j.val 55207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_55207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55207) = 59049 * m + 49744 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 55207
  rw [data_16_55207.1, data_16_55207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_55207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55207) < 65536 * m + 55207 := by
  apply descent_of_endpoint
  · rw [data_16_55207.1]; exact data_16_55207.2.2
  · rw [data_16_55207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 55291). -/
theorem data_16_55291 : oddCount 55291 16 = 10 ∧
    acceleratedOrbit 16 55291 = 49820 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_55291 : ∀ j : Fin 16,
    55291 ≤ acceleratedOrbit j.val 55291 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_55291 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55291) = 59049 * m + 49820 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 55291
  rw [data_16_55291.1, data_16_55291.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_55291 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55291) < 65536 * m + 55291 := by
  apply descent_of_endpoint
  · rw [data_16_55291.1]; exact data_16_55291.2.2
  · rw [data_16_55291.2.1]; decide

end Collatz.Research.FirstDescent.Batch089
