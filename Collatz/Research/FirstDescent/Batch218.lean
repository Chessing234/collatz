import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 218. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch218
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 259455). -/
theorem data_18_259455 : oddCount 259455 18 = 11 ∧
    acceleratedOrbit 18 259455 = 175331 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_259455 : ∀ j : Fin 18,
    259455 ≤ acceleratedOrbit j.val 259455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_259455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 259455) = 177147 * m + 175331 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 259455
  rw [data_18_259455.1, data_18_259455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_259455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 259455) < 262144 * m + 259455 := by
  apply descent_of_endpoint
  · rw [data_18_259455.1]; exact data_18_259455.2.2
  · rw [data_18_259455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 260319). -/
theorem data_18_260319 : oddCount 260319 18 = 11 ∧
    acceleratedOrbit 18 260319 = 175915 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_260319 : ∀ j : Fin 18,
    260319 ≤ acceleratedOrbit j.val 260319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_260319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260319) = 177147 * m + 175915 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 260319
  rw [data_18_260319.1, data_18_260319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_260319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260319) < 262144 * m + 260319 := by
  apply descent_of_endpoint
  · rw [data_18_260319.1]; exact data_18_260319.2.2
  · rw [data_18_260319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 260347). -/
theorem data_18_260347 : oddCount 260347 18 = 11 ∧
    acceleratedOrbit 18 260347 = 175934 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_260347 : ∀ j : Fin 18,
    260347 ≤ acceleratedOrbit j.val 260347 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_260347 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260347) = 177147 * m + 175934 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 260347
  rw [data_18_260347.1, data_18_260347.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_260347 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260347) < 262144 * m + 260347 := by
  apply descent_of_endpoint
  · rw [data_18_260347.1]; exact data_18_260347.2.2
  · rw [data_18_260347.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 260479). -/
theorem data_18_260479 : oddCount 260479 18 = 11 ∧
    acceleratedOrbit 18 260479 = 176023 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_260479 : ∀ j : Fin 18,
    260479 ≤ acceleratedOrbit j.val 260479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_260479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260479) = 177147 * m + 176023 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 260479
  rw [data_18_260479.1, data_18_260479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_260479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260479) < 262144 * m + 260479 := by
  apply descent_of_endpoint
  · rw [data_18_260479.1]; exact data_18_260479.2.2
  · rw [data_18_260479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 260711). -/
theorem data_18_260711 : oddCount 260711 18 = 11 ∧
    acceleratedOrbit 18 260711 = 176180 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_260711 : ∀ j : Fin 18,
    260711 ≤ acceleratedOrbit j.val 260711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_260711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260711) = 177147 * m + 176180 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 260711
  rw [data_18_260711.1, data_18_260711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_260711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260711) < 262144 * m + 260711 := by
  apply descent_of_endpoint
  · rw [data_18_260711.1]; exact data_18_260711.2.2
  · rw [data_18_260711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 260799). -/
theorem data_18_260799 : oddCount 260799 18 = 11 ∧
    acceleratedOrbit 18 260799 = 176239 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_260799 : ∀ j : Fin 18,
    260799 ≤ acceleratedOrbit j.val 260799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_260799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260799) = 177147 * m + 176239 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 260799
  rw [data_18_260799.1, data_18_260799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_260799 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 260799) < 262144 * m + 260799 := by
  apply descent_of_endpoint
  · rw [data_18_260799.1]; exact data_18_260799.2.2
  · rw [data_18_260799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 261151). -/
theorem data_18_261151 : oddCount 261151 18 = 11 ∧
    acceleratedOrbit 18 261151 = 176477 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_261151 : ∀ j : Fin 18,
    261151 ≤ acceleratedOrbit j.val 261151 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_261151 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261151) = 177147 * m + 176477 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 261151
  rw [data_18_261151.1, data_18_261151.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_261151 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261151) < 262144 * m + 261151 := by
  apply descent_of_endpoint
  · rw [data_18_261151.1]; exact data_18_261151.2.2
  · rw [data_18_261151.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 261231). -/
theorem data_18_261231 : oddCount 261231 18 = 11 ∧
    acceleratedOrbit 18 261231 = 176531 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_261231 : ∀ j : Fin 18,
    261231 ≤ acceleratedOrbit j.val 261231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_261231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261231) = 177147 * m + 176531 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 261231
  rw [data_18_261231.1, data_18_261231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_261231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261231) < 262144 * m + 261231 := by
  apply descent_of_endpoint
  · rw [data_18_261231.1]; exact data_18_261231.2.2
  · rw [data_18_261231.2.1]; decide

end Collatz.Research.FirstDescent.Batch218
