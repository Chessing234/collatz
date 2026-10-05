import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 84. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch084
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 48987). -/
theorem data_16_48987 : oddCount 48987 16 = 10 ∧
    acceleratedOrbit 16 48987 = 44140 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_48987 : ∀ j : Fin 16,
    48987 ≤ acceleratedOrbit j.val 48987 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_48987 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48987) = 59049 * m + 44140 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 48987
  rw [data_16_48987.1, data_16_48987.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_48987 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 48987) < 65536 * m + 48987 := by
  apply descent_of_endpoint
  · rw [data_16_48987.1]; exact data_16_48987.2.2
  · rw [data_16_48987.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 49135). -/
theorem data_16_49135 : oddCount 49135 16 = 10 ∧
    acceleratedOrbit 16 49135 = 44273 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_49135 : ∀ j : Fin 16,
    49135 ≤ acceleratedOrbit j.val 49135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_49135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49135) = 59049 * m + 44273 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 49135
  rw [data_16_49135.1, data_16_49135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_49135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49135) < 65536 * m + 49135 := by
  apply descent_of_endpoint
  · rw [data_16_49135.1]; exact data_16_49135.2.2
  · rw [data_16_49135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 49215). -/
theorem data_16_49215 : oddCount 49215 16 = 10 ∧
    acceleratedOrbit 16 49215 = 44345 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_49215 : ∀ j : Fin 16,
    49215 ≤ acceleratedOrbit j.val 49215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_49215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49215) = 59049 * m + 44345 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 49215
  rw [data_16_49215.1, data_16_49215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_49215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49215) < 65536 * m + 49215 := by
  apply descent_of_endpoint
  · rw [data_16_49215.1]; exact data_16_49215.2.2
  · rw [data_16_49215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 49255). -/
theorem data_16_49255 : oddCount 49255 16 = 10 ∧
    acceleratedOrbit 16 49255 = 44381 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_49255 : ∀ j : Fin 16,
    49255 ≤ acceleratedOrbit j.val 49255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_49255 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49255) = 59049 * m + 44381 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 49255
  rw [data_16_49255.1, data_16_49255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_49255 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49255) < 65536 * m + 49255 := by
  apply descent_of_endpoint
  · rw [data_16_49255.1]; exact data_16_49255.2.2
  · rw [data_16_49255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 49311). -/
theorem data_16_49311 : oddCount 49311 16 = 10 ∧
    acceleratedOrbit 16 49311 = 44431 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_49311 : ∀ j : Fin 16,
    49311 ≤ acceleratedOrbit j.val 49311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_49311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49311) = 59049 * m + 44431 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 49311
  rw [data_16_49311.1, data_16_49311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_49311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49311) < 65536 * m + 49311 := by
  apply descent_of_endpoint
  · rw [data_16_49311.1]; exact data_16_49311.2.2
  · rw [data_16_49311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 49563). -/
theorem data_16_49563 : oddCount 49563 16 = 10 ∧
    acceleratedOrbit 16 49563 = 44659 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_49563 : ∀ j : Fin 16,
    49563 ≤ acceleratedOrbit j.val 49563 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_49563 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49563) = 59049 * m + 44659 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 49563
  rw [data_16_49563.1, data_16_49563.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_49563 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49563) < 65536 * m + 49563 := by
  apply descent_of_endpoint
  · rw [data_16_49563.1]; exact data_16_49563.2.2
  · rw [data_16_49563.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 49567). -/
theorem data_16_49567 : oddCount 49567 16 = 10 ∧
    acceleratedOrbit 16 49567 = 44662 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_49567 : ∀ j : Fin 16,
    49567 ≤ acceleratedOrbit j.val 49567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_49567 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49567) = 59049 * m + 44662 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 49567
  rw [data_16_49567.1, data_16_49567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_49567 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49567) < 65536 * m + 49567 := by
  apply descent_of_endpoint
  · rw [data_16_49567.1]; exact data_16_49567.2.2
  · rw [data_16_49567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 49983). -/
theorem data_16_49983 : oddCount 49983 16 = 10 ∧
    acceleratedOrbit 16 49983 = 45037 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_49983 : ∀ j : Fin 16,
    49983 ≤ acceleratedOrbit j.val 49983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_49983 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49983) = 59049 * m + 45037 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 49983
  rw [data_16_49983.1, data_16_49983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_49983 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 49983) < 65536 * m + 49983 := by
  apply descent_of_endpoint
  · rw [data_16_49983.1]; exact data_16_49983.2.2
  · rw [data_16_49983.2.1]; decide

end Collatz.Research.FirstDescent.Batch084
