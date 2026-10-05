import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 299. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch299
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 236391). -/
theorem data_20_236391 : oddCount 236391 20 = 12 ∧
    acceleratedOrbit 20 236391 = 119809 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_236391 : ∀ j : Fin 20,
    236391 ≤ acceleratedOrbit j.val 236391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_236391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 236391) = 531441 * m + 119809 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 236391
  rw [data_20_236391.1, data_20_236391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_236391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 236391) < 1048576 * m + 236391 := by
  apply descent_of_endpoint
  · rw [data_20_236391.1]; exact data_20_236391.2.2
  · rw [data_20_236391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 237979). -/
theorem data_20_237979 : oddCount 237979 20 = 12 ∧
    acceleratedOrbit 20 237979 = 120614 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_237979 : ∀ j : Fin 20,
    237979 ≤ acceleratedOrbit j.val 237979 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_237979 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 237979) = 531441 * m + 120614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 237979
  rw [data_20_237979.1, data_20_237979.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_237979 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 237979) < 1048576 * m + 237979 := by
  apply descent_of_endpoint
  · rw [data_20_237979.1]; exact data_20_237979.2.2
  · rw [data_20_237979.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 238335). -/
theorem data_20_238335 : oddCount 238335 20 = 12 ∧
    acceleratedOrbit 20 238335 = 120794 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_238335 : ∀ j : Fin 20,
    238335 ≤ acceleratedOrbit j.val 238335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_238335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238335) = 531441 * m + 120794 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 238335
  rw [data_20_238335.1, data_20_238335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_238335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238335) < 1048576 * m + 238335 := by
  apply descent_of_endpoint
  · rw [data_20_238335.1]; exact data_20_238335.2.2
  · rw [data_20_238335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 238575). -/
theorem data_20_238575 : oddCount 238575 20 = 12 ∧
    acceleratedOrbit 20 238575 = 120916 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_238575 : ∀ j : Fin 20,
    238575 ≤ acceleratedOrbit j.val 238575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_238575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238575) = 531441 * m + 120916 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 238575
  rw [data_20_238575.1, data_20_238575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_238575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238575) < 1048576 * m + 238575 := by
  apply descent_of_endpoint
  · rw [data_20_238575.1]; exact data_20_238575.2.2
  · rw [data_20_238575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 238623). -/
theorem data_20_238623 : oddCount 238623 20 = 12 ∧
    acceleratedOrbit 20 238623 = 120940 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_238623 : ∀ j : Fin 20,
    238623 ≤ acceleratedOrbit j.val 238623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_238623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238623) = 531441 * m + 120940 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 238623
  rw [data_20_238623.1, data_20_238623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_238623 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238623) < 1048576 * m + 238623 := by
  apply descent_of_endpoint
  · rw [data_20_238623.1]; exact data_20_238623.2.2
  · rw [data_20_238623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 238843). -/
theorem data_20_238843 : oddCount 238843 20 = 12 ∧
    acceleratedOrbit 20 238843 = 121052 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_238843 : ∀ j : Fin 20,
    238843 ≤ acceleratedOrbit j.val 238843 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_238843 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238843) = 531441 * m + 121052 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 238843
  rw [data_20_238843.1, data_20_238843.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_238843 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 238843) < 1048576 * m + 238843 := by
  apply descent_of_endpoint
  · rw [data_20_238843.1]; exact data_20_238843.2.2
  · rw [data_20_238843.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 239311). -/
theorem data_20_239311 : oddCount 239311 20 = 12 ∧
    acceleratedOrbit 20 239311 = 121289 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_239311 : ∀ j : Fin 20,
    239311 ≤ acceleratedOrbit j.val 239311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_239311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239311) = 531441 * m + 121289 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 239311
  rw [data_20_239311.1, data_20_239311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_239311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239311) < 1048576 * m + 239311 := by
  apply descent_of_endpoint
  · rw [data_20_239311.1]; exact data_20_239311.2.2
  · rw [data_20_239311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 239359). -/
theorem data_20_239359 : oddCount 239359 20 = 12 ∧
    acceleratedOrbit 20 239359 = 121313 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_239359 : ∀ j : Fin 20,
    239359 ≤ acceleratedOrbit j.val 239359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_239359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239359) = 531441 * m + 121313 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 239359
  rw [data_20_239359.1, data_20_239359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_239359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239359) < 1048576 * m + 239359 := by
  apply descent_of_endpoint
  · rw [data_20_239359.1]; exact data_20_239359.2.2
  · rw [data_20_239359.2.1]; decide

end Collatz.Research.FirstDescent.Batch299
