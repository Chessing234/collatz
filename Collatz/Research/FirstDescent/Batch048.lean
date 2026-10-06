import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 48. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch048
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 8863). -/
theorem data_16_8863 : oddCount 8863 16 = 10 ∧
    acceleratedOrbit 16 8863 = 7987 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_8863 : ∀ j : Fin 16,
    8863 ≤ acceleratedOrbit j.val 8863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_8863 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8863) = 59049 * m + 7987 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 8863
  rw [data_16_8863.1, data_16_8863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_8863 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8863) < 65536 * m + 8863 := by
  apply descent_of_endpoint
  · rw [data_16_8863.1]; exact data_16_8863.2.2
  · rw [data_16_8863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 9119). -/
theorem data_16_9119 : oddCount 9119 16 = 10 ∧
    acceleratedOrbit 16 9119 = 8218 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_9119 : ∀ j : Fin 16,
    9119 ≤ acceleratedOrbit j.val 9119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_9119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9119) = 59049 * m + 8218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 9119
  rw [data_16_9119.1, data_16_9119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_9119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9119) < 65536 * m + 9119 := by
  apply descent_of_endpoint
  · rw [data_16_9119.1]; exact data_16_9119.2.2
  · rw [data_16_9119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 9199). -/
theorem data_16_9199 : oddCount 9199 16 = 10 ∧
    acceleratedOrbit 16 9199 = 8290 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_9199 : ∀ j : Fin 16,
    9199 ≤ acceleratedOrbit j.val 9199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_9199 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9199) = 59049 * m + 8290 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 9199
  rw [data_16_9199.1, data_16_9199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_9199 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9199) < 65536 * m + 9199 := by
  apply descent_of_endpoint
  · rw [data_16_9199.1]; exact data_16_9199.2.2
  · rw [data_16_9199.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 9319). -/
theorem data_16_9319 : oddCount 9319 16 = 10 ∧
    acceleratedOrbit 16 9319 = 8398 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_9319 : ∀ j : Fin 16,
    9319 ≤ acceleratedOrbit j.val 9319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_9319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9319) = 59049 * m + 8398 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 9319
  rw [data_16_9319.1, data_16_9319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_9319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9319) < 65536 * m + 9319 := by
  apply descent_of_endpoint
  · rw [data_16_9319.1]; exact data_16_9319.2.2
  · rw [data_16_9319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 9543). -/
theorem data_16_9543 : oddCount 9543 16 = 10 ∧
    acceleratedOrbit 16 9543 = 8600 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_9543 : ∀ j : Fin 16,
    9543 ≤ acceleratedOrbit j.val 9543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_9543 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9543) = 59049 * m + 8600 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 9543
  rw [data_16_9543.1, data_16_9543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_9543 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9543) < 65536 * m + 9543 := by
  apply descent_of_endpoint
  · rw [data_16_9543.1]; exact data_16_9543.2.2
  · rw [data_16_9543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 9599). -/
theorem data_16_9599 : oddCount 9599 16 = 10 ∧
    acceleratedOrbit 16 9599 = 8650 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_9599 : ∀ j : Fin 16,
    9599 ≤ acceleratedOrbit j.val 9599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_9599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9599) = 59049 * m + 8650 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 9599
  rw [data_16_9599.1, data_16_9599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_9599 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9599) < 65536 * m + 9599 := by
  apply descent_of_endpoint
  · rw [data_16_9599.1]; exact data_16_9599.2.2
  · rw [data_16_9599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 9819). -/
theorem data_16_9819 : oddCount 9819 16 = 10 ∧
    acceleratedOrbit 16 9819 = 8849 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_9819 : ∀ j : Fin 16,
    9819 ≤ acceleratedOrbit j.val 9819 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_9819 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9819) = 59049 * m + 8849 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 9819
  rw [data_16_9819.1, data_16_9819.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_9819 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9819) < 65536 * m + 9819 := by
  apply descent_of_endpoint
  · rw [data_16_9819.1]; exact data_16_9819.2.2
  · rw [data_16_9819.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 9935). -/
theorem data_16_9935 : oddCount 9935 16 = 10 ∧
    acceleratedOrbit 16 9935 = 8953 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_9935 : ∀ j : Fin 16,
    9935 ≤ acceleratedOrbit j.val 9935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_9935 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9935) = 59049 * m + 8953 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 9935
  rw [data_16_9935.1, data_16_9935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_9935 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 9935) < 65536 * m + 9935 := by
  apply descent_of_endpoint
  · rw [data_16_9935.1]; exact data_16_9935.2.2
  · rw [data_16_9935.2.1]; decide

end Collatz.Research.FirstDescent.Batch048
