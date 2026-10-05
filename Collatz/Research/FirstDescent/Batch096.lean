import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 96. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch096
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61723). -/
theorem data_16_61723 : oddCount 61723 16 = 10 ∧
    acceleratedOrbit 16 61723 = 55615 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61723 : ∀ j : Fin 16,
    61723 ≤ acceleratedOrbit j.val 61723 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61723 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61723) = 59049 * m + 55615 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61723
  rw [data_16_61723.1, data_16_61723.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61723 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61723) < 65536 * m + 61723 := by
  apply descent_of_endpoint
  · rw [data_16_61723.1]; exact data_16_61723.2.2
  · rw [data_16_61723.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 61979). -/
theorem data_16_61979 : oddCount 61979 16 = 10 ∧
    acceleratedOrbit 16 61979 = 55846 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_61979 : ∀ j : Fin 16,
    61979 ≤ acceleratedOrbit j.val 61979 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_61979 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61979) = 59049 * m + 55846 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 61979
  rw [data_16_61979.1, data_16_61979.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_61979 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 61979) < 65536 * m + 61979 := by
  apply descent_of_endpoint
  · rw [data_16_61979.1]; exact data_16_61979.2.2
  · rw [data_16_61979.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 62119). -/
theorem data_16_62119 : oddCount 62119 16 = 10 ∧
    acceleratedOrbit 16 62119 = 55972 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_62119 : ∀ j : Fin 16,
    62119 ≤ acceleratedOrbit j.val 62119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_62119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62119) = 59049 * m + 55972 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 62119
  rw [data_16_62119.1, data_16_62119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_62119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62119) < 65536 * m + 62119 := by
  apply descent_of_endpoint
  · rw [data_16_62119.1]; exact data_16_62119.2.2
  · rw [data_16_62119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 62159). -/
theorem data_16_62159 : oddCount 62159 16 = 10 ∧
    acceleratedOrbit 16 62159 = 56008 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_62159 : ∀ j : Fin 16,
    62159 ≤ acceleratedOrbit j.val 62159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_62159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62159) = 59049 * m + 56008 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 62159
  rw [data_16_62159.1, data_16_62159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_62159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62159) < 65536 * m + 62159 := by
  apply descent_of_endpoint
  · rw [data_16_62159.1]; exact data_16_62159.2.2
  · rw [data_16_62159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 62239). -/
theorem data_16_62239 : oddCount 62239 16 = 10 ∧
    acceleratedOrbit 16 62239 = 56080 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_62239 : ∀ j : Fin 16,
    62239 ≤ acceleratedOrbit j.val 62239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_62239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62239) = 59049 * m + 56080 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 62239
  rw [data_16_62239.1, data_16_62239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_62239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62239) < 65536 * m + 62239 := by
  apply descent_of_endpoint
  · rw [data_16_62239.1]; exact data_16_62239.2.2
  · rw [data_16_62239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 62279). -/
theorem data_16_62279 : oddCount 62279 16 = 10 ∧
    acceleratedOrbit 16 62279 = 56116 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_62279 : ∀ j : Fin 16,
    62279 ≤ acceleratedOrbit j.val 62279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_62279 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62279) = 59049 * m + 56116 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 62279
  rw [data_16_62279.1, data_16_62279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_62279 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62279) < 65536 * m + 62279 := by
  apply descent_of_endpoint
  · rw [data_16_62279.1]; exact data_16_62279.2.2
  · rw [data_16_62279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 62719). -/
theorem data_16_62719 : oddCount 62719 16 = 10 ∧
    acceleratedOrbit 16 62719 = 56512 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_62719 : ∀ j : Fin 16,
    62719 ≤ acceleratedOrbit j.val 62719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_62719 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62719) = 59049 * m + 56512 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 62719
  rw [data_16_62719.1, data_16_62719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_62719 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62719) < 65536 * m + 62719 := by
  apply descent_of_endpoint
  · rw [data_16_62719.1]; exact data_16_62719.2.2
  · rw [data_16_62719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 62943). -/
theorem data_16_62943 : oddCount 62943 16 = 10 ∧
    acceleratedOrbit 16 62943 = 56714 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_62943 : ∀ j : Fin 16,
    62943 ≤ acceleratedOrbit j.val 62943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_62943 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62943) = 59049 * m + 56714 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 62943
  rw [data_16_62943.1, data_16_62943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_62943 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 62943) < 65536 * m + 62943 := by
  apply descent_of_endpoint
  · rw [data_16_62943.1]; exact data_16_62943.2.2
  · rw [data_16_62943.2.1]; decide

end Collatz.Research.FirstDescent.Batch096
