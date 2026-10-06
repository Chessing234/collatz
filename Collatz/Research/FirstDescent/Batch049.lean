import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 49. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch049
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 10151). -/
theorem data_16_10151 : oddCount 10151 16 = 10 ∧
    acceleratedOrbit 16 10151 = 9148 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_10151 : ∀ j : Fin 16,
    10151 ≤ acceleratedOrbit j.val 10151 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_10151 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10151) = 59049 * m + 9148 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 10151
  rw [data_16_10151.1, data_16_10151.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_10151 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10151) < 65536 * m + 10151 := by
  apply descent_of_endpoint
  · rw [data_16_10151.1]; exact data_16_10151.2.2
  · rw [data_16_10151.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 10559). -/
theorem data_16_10559 : oddCount 10559 16 = 10 ∧
    acceleratedOrbit 16 10559 = 9515 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_10559 : ∀ j : Fin 16,
    10559 ≤ acceleratedOrbit j.val 10559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_10559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10559) = 59049 * m + 9515 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 10559
  rw [data_16_10559.1, data_16_10559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_10559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10559) < 65536 * m + 10559 := by
  apply descent_of_endpoint
  · rw [data_16_10559.1]; exact data_16_10559.2.2
  · rw [data_16_10559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 10727). -/
theorem data_16_10727 : oddCount 10727 16 = 10 ∧
    acceleratedOrbit 16 10727 = 9667 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_10727 : ∀ j : Fin 16,
    10727 ≤ acceleratedOrbit j.val 10727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_10727 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10727) = 59049 * m + 9667 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 10727
  rw [data_16_10727.1, data_16_10727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_10727 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10727) < 65536 * m + 10727 := by
  apply descent_of_endpoint
  · rw [data_16_10727.1]; exact data_16_10727.2.2
  · rw [data_16_10727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 10907). -/
theorem data_16_10907 : oddCount 10907 16 = 10 ∧
    acceleratedOrbit 16 10907 = 9829 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_10907 : ∀ j : Fin 16,
    10907 ≤ acceleratedOrbit j.val 10907 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_10907 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10907) = 59049 * m + 9829 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 10907
  rw [data_16_10907.1, data_16_10907.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_10907 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 10907) < 65536 * m + 10907 := by
  apply descent_of_endpoint
  · rw [data_16_10907.1]; exact data_16_10907.2.2
  · rw [data_16_10907.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 11035). -/
theorem data_16_11035 : oddCount 11035 16 = 10 ∧
    acceleratedOrbit 16 11035 = 9944 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_11035 : ∀ j : Fin 16,
    11035 ≤ acceleratedOrbit j.val 11035 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_11035 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11035) = 59049 * m + 9944 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 11035
  rw [data_16_11035.1, data_16_11035.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_11035 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11035) < 65536 * m + 11035 := by
  apply descent_of_endpoint
  · rw [data_16_11035.1]; exact data_16_11035.2.2
  · rw [data_16_11035.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 11247). -/
theorem data_16_11247 : oddCount 11247 16 = 10 ∧
    acceleratedOrbit 16 11247 = 10135 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_11247 : ∀ j : Fin 16,
    11247 ≤ acceleratedOrbit j.val 11247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_11247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11247) = 59049 * m + 10135 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 11247
  rw [data_16_11247.1, data_16_11247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_11247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11247) < 65536 * m + 11247 := by
  apply descent_of_endpoint
  · rw [data_16_11247.1]; exact data_16_11247.2.2
  · rw [data_16_11247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 11431). -/
theorem data_16_11431 : oddCount 11431 16 = 10 ∧
    acceleratedOrbit 16 11431 = 10301 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_11431 : ∀ j : Fin 16,
    11431 ≤ acceleratedOrbit j.val 11431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_11431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11431) = 59049 * m + 10301 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 11431
  rw [data_16_11431.1, data_16_11431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_11431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11431) < 65536 * m + 11431 := by
  apply descent_of_endpoint
  · rw [data_16_11431.1]; exact data_16_11431.2.2
  · rw [data_16_11431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 11727). -/
theorem data_16_11727 : oddCount 11727 16 = 10 ∧
    acceleratedOrbit 16 11727 = 10568 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_11727 : ∀ j : Fin 16,
    11727 ≤ acceleratedOrbit j.val 11727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_11727 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11727) = 59049 * m + 10568 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 11727
  rw [data_16_11727.1, data_16_11727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_11727 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 11727) < 65536 * m + 11727 := by
  apply descent_of_endpoint
  · rw [data_16_11727.1]; exact data_16_11727.2.2
  · rw [data_16_11727.2.1]; decide

end Collatz.Research.FirstDescent.Batch049
