import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 65. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch065
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27879). -/
theorem data_16_27879 : oddCount 27879 16 = 10 ∧
    acceleratedOrbit 16 27879 = 25121 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27879 : ∀ j : Fin 16,
    27879 ≤ acceleratedOrbit j.val 27879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27879 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27879) = 59049 * m + 25121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27879
  rw [data_16_27879.1, data_16_27879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27879 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27879) < 65536 * m + 27879 := by
  apply descent_of_endpoint
  · rw [data_16_27879.1]; exact data_16_27879.2.2
  · rw [data_16_27879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27903). -/
theorem data_16_27903 : oddCount 27903 16 = 10 ∧
    acceleratedOrbit 16 27903 = 25142 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27903 : ∀ j : Fin 16,
    27903 ≤ acceleratedOrbit j.val 27903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27903 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27903) = 59049 * m + 25142 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27903
  rw [data_16_27903.1, data_16_27903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27903 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27903) < 65536 * m + 27903 := by
  apply descent_of_endpoint
  · rw [data_16_27903.1]; exact data_16_27903.2.2
  · rw [data_16_27903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 27951). -/
theorem data_16_27951 : oddCount 27951 16 = 10 ∧
    acceleratedOrbit 16 27951 = 25186 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_27951 : ∀ j : Fin 16,
    27951 ≤ acceleratedOrbit j.val 27951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_27951 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27951) = 59049 * m + 25186 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 27951
  rw [data_16_27951.1, data_16_27951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_27951 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 27951) < 65536 * m + 27951 := by
  apply descent_of_endpoint
  · rw [data_16_27951.1]; exact data_16_27951.2.2
  · rw [data_16_27951.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28095). -/
theorem data_16_28095 : oddCount 28095 16 = 10 ∧
    acceleratedOrbit 16 28095 = 25315 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28095 : ∀ j : Fin 16,
    28095 ≤ acceleratedOrbit j.val 28095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28095 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28095) = 59049 * m + 25315 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28095
  rw [data_16_28095.1, data_16_28095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28095 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28095) < 65536 * m + 28095 := by
  apply descent_of_endpoint
  · rw [data_16_28095.1]; exact data_16_28095.2.2
  · rw [data_16_28095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28191). -/
theorem data_16_28191 : oddCount 28191 16 = 10 ∧
    acceleratedOrbit 16 28191 = 25402 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28191 : ∀ j : Fin 16,
    28191 ≤ acceleratedOrbit j.val 28191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28191 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28191) = 59049 * m + 25402 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28191
  rw [data_16_28191.1, data_16_28191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28191 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28191) < 65536 * m + 28191 := by
  apply descent_of_endpoint
  · rw [data_16_28191.1]; exact data_16_28191.2.2
  · rw [data_16_28191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28319). -/
theorem data_16_28319 : oddCount 28319 16 = 10 ∧
    acceleratedOrbit 16 28319 = 25517 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28319 : ∀ j : Fin 16,
    28319 ≤ acceleratedOrbit j.val 28319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28319) = 59049 * m + 25517 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28319
  rw [data_16_28319.1, data_16_28319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28319 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28319) < 65536 * m + 28319 := by
  apply descent_of_endpoint
  · rw [data_16_28319.1]; exact data_16_28319.2.2
  · rw [data_16_28319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28327). -/
theorem data_16_28327 : oddCount 28327 16 = 10 ∧
    acceleratedOrbit 16 28327 = 25525 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28327 : ∀ j : Fin 16,
    28327 ≤ acceleratedOrbit j.val 28327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28327 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28327) = 59049 * m + 25525 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28327
  rw [data_16_28327.1, data_16_28327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28327 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28327) < 65536 * m + 28327 := by
  apply descent_of_endpoint
  · rw [data_16_28327.1]; exact data_16_28327.2.2
  · rw [data_16_28327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 28351). -/
theorem data_16_28351 : oddCount 28351 16 = 10 ∧
    acceleratedOrbit 16 28351 = 25546 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_28351 : ∀ j : Fin 16,
    28351 ≤ acceleratedOrbit j.val 28351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_28351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28351) = 59049 * m + 25546 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 28351
  rw [data_16_28351.1, data_16_28351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_28351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 28351) < 65536 * m + 28351 := by
  apply descent_of_endpoint
  · rw [data_16_28351.1]; exact data_16_28351.2.2
  · rw [data_16_28351.2.1]; decide

end Collatz.Research.FirstDescent.Batch065
