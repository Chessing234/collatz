import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 88. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch088
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52763). -/
theorem data_16_52763 : oddCount 52763 16 = 10 ∧
    acceleratedOrbit 16 52763 = 47542 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52763 : ∀ j : Fin 16,
    52763 ≤ acceleratedOrbit j.val 52763 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52763 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52763) = 59049 * m + 47542 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52763
  rw [data_16_52763.1, data_16_52763.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52763 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52763) < 65536 * m + 52763 := by
  apply descent_of_endpoint
  · rw [data_16_52763.1]; exact data_16_52763.2.2
  · rw [data_16_52763.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 53159). -/
theorem data_16_53159 : oddCount 53159 16 = 10 ∧
    acceleratedOrbit 16 53159 = 47899 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_53159 : ∀ j : Fin 16,
    53159 ≤ acceleratedOrbit j.val 53159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_53159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53159) = 59049 * m + 47899 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 53159
  rw [data_16_53159.1, data_16_53159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_53159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53159) < 65536 * m + 53159 := by
  apply descent_of_endpoint
  · rw [data_16_53159.1]; exact data_16_53159.2.2
  · rw [data_16_53159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 53183). -/
theorem data_16_53183 : oddCount 53183 16 = 10 ∧
    acceleratedOrbit 16 53183 = 47920 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_53183 : ∀ j : Fin 16,
    53183 ≤ acceleratedOrbit j.val 53183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_53183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53183) = 59049 * m + 47920 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 53183
  rw [data_16_53183.1, data_16_53183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_53183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53183) < 65536 * m + 53183 := by
  apply descent_of_endpoint
  · rw [data_16_53183.1]; exact data_16_53183.2.2
  · rw [data_16_53183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 53319). -/
theorem data_16_53319 : oddCount 53319 16 = 10 ∧
    acceleratedOrbit 16 53319 = 48043 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_53319 : ∀ j : Fin 16,
    53319 ≤ acceleratedOrbit j.val 53319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_53319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53319) = 59049 * m + 48043 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 53319
  rw [data_16_53319.1, data_16_53319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_53319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53319) < 65536 * m + 53319 := by
  apply descent_of_endpoint
  · rw [data_16_53319.1]; exact data_16_53319.2.2
  · rw [data_16_53319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 53339). -/
theorem data_16_53339 : oddCount 53339 16 = 10 ∧
    acceleratedOrbit 16 53339 = 48061 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_53339 : ∀ j : Fin 16,
    53339 ≤ acceleratedOrbit j.val 53339 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_53339 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53339) = 59049 * m + 48061 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 53339
  rw [data_16_53339.1, data_16_53339.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_53339 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53339) < 65536 * m + 53339 := by
  apply descent_of_endpoint
  · rw [data_16_53339.1]; exact data_16_53339.2.2
  · rw [data_16_53339.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 53439). -/
theorem data_16_53439 : oddCount 53439 16 = 10 ∧
    acceleratedOrbit 16 53439 = 48151 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_53439 : ∀ j : Fin 16,
    53439 ≤ acceleratedOrbit j.val 53439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_53439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53439) = 59049 * m + 48151 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 53439
  rw [data_16_53439.1, data_16_53439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_53439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53439) < 65536 * m + 53439 := by
  apply descent_of_endpoint
  · rw [data_16_53439.1]; exact data_16_53439.2.2
  · rw [data_16_53439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 53887). -/
theorem data_16_53887 : oddCount 53887 16 = 10 ∧
    acceleratedOrbit 16 53887 = 48554 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_53887 : ∀ j : Fin 16,
    53887 ≤ acceleratedOrbit j.val 53887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_53887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53887) = 59049 * m + 48554 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 53887
  rw [data_16_53887.1, data_16_53887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_53887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53887) < 65536 * m + 53887 := by
  apply descent_of_endpoint
  · rw [data_16_53887.1]; exact data_16_53887.2.2
  · rw [data_16_53887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 53919). -/
theorem data_16_53919 : oddCount 53919 16 = 10 ∧
    acceleratedOrbit 16 53919 = 48583 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_53919 : ∀ j : Fin 16,
    53919 ≤ acceleratedOrbit j.val 53919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_53919 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53919) = 59049 * m + 48583 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 53919
  rw [data_16_53919.1, data_16_53919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_53919 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 53919) < 65536 * m + 53919 := by
  apply descent_of_endpoint
  · rw [data_16_53919.1]; exact data_16_53919.2.2
  · rw [data_16_53919.2.1]; decide

end Collatz.Research.FirstDescent.Batch088
