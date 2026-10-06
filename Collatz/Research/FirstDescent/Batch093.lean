import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 93. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch093
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 58863). -/
theorem data_16_58863 : oddCount 58863 16 = 10 ∧
    acceleratedOrbit 16 58863 = 53038 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_58863 : ∀ j : Fin 16,
    58863 ≤ acceleratedOrbit j.val 58863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_58863 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58863) = 59049 * m + 53038 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 58863
  rw [data_16_58863.1, data_16_58863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_58863 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58863) < 65536 * m + 58863 := by
  apply descent_of_endpoint
  · rw [data_16_58863.1]; exact data_16_58863.2.2
  · rw [data_16_58863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 58983). -/
theorem data_16_58983 : oddCount 58983 16 = 10 ∧
    acceleratedOrbit 16 58983 = 53146 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_58983 : ∀ j : Fin 16,
    58983 ≤ acceleratedOrbit j.val 58983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_58983 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58983) = 59049 * m + 53146 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 58983
  rw [data_16_58983.1, data_16_58983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_58983 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 58983) < 65536 * m + 58983 := by
  apply descent_of_endpoint
  · rw [data_16_58983.1]; exact data_16_58983.2.2
  · rw [data_16_58983.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 59247). -/
theorem data_16_59247 : oddCount 59247 16 = 10 ∧
    acceleratedOrbit 16 59247 = 53384 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_59247 : ∀ j : Fin 16,
    59247 ≤ acceleratedOrbit j.val 59247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_59247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59247) = 59049 * m + 53384 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 59247
  rw [data_16_59247.1, data_16_59247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_59247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59247) < 65536 * m + 59247 := by
  apply descent_of_endpoint
  · rw [data_16_59247.1]; exact data_16_59247.2.2
  · rw [data_16_59247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 59263). -/
theorem data_16_59263 : oddCount 59263 16 = 10 ∧
    acceleratedOrbit 16 59263 = 53398 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_59263 : ∀ j : Fin 16,
    59263 ≤ acceleratedOrbit j.val 59263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_59263 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59263) = 59049 * m + 53398 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 59263
  rw [data_16_59263.1, data_16_59263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_59263 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59263) < 65536 * m + 59263 := by
  apply descent_of_endpoint
  · rw [data_16_59263.1]; exact data_16_59263.2.2
  · rw [data_16_59263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 59463). -/
theorem data_16_59463 : oddCount 59463 16 = 10 ∧
    acceleratedOrbit 16 59463 = 53579 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_59463 : ∀ j : Fin 16,
    59463 ≤ acceleratedOrbit j.val 59463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_59463 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59463) = 59049 * m + 53579 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 59463
  rw [data_16_59463.1, data_16_59463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_59463 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59463) < 65536 * m + 59463 := by
  apply descent_of_endpoint
  · rw [data_16_59463.1]; exact data_16_59463.2.2
  · rw [data_16_59463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 59559). -/
theorem data_16_59559 : oddCount 59559 16 = 10 ∧
    acceleratedOrbit 16 59559 = 53665 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_59559 : ∀ j : Fin 16,
    59559 ≤ acceleratedOrbit j.val 59559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_59559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59559) = 59049 * m + 53665 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 59559
  rw [data_16_59559.1, data_16_59559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_59559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59559) < 65536 * m + 59559 := by
  apply descent_of_endpoint
  · rw [data_16_59559.1]; exact data_16_59559.2.2
  · rw [data_16_59559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 59623). -/
theorem data_16_59623 : oddCount 59623 16 = 10 ∧
    acceleratedOrbit 16 59623 = 53723 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_59623 : ∀ j : Fin 16,
    59623 ≤ acceleratedOrbit j.val 59623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_59623 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59623) = 59049 * m + 53723 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 59623
  rw [data_16_59623.1, data_16_59623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_59623 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59623) < 65536 * m + 59623 := by
  apply descent_of_endpoint
  · rw [data_16_59623.1]; exact data_16_59623.2.2
  · rw [data_16_59623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 59643). -/
theorem data_16_59643 : oddCount 59643 16 = 10 ∧
    acceleratedOrbit 16 59643 = 53741 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_59643 : ∀ j : Fin 16,
    59643 ≤ acceleratedOrbit j.val 59643 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_59643 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59643) = 59049 * m + 53741 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 59643
  rw [data_16_59643.1, data_16_59643.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_59643 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59643) < 65536 * m + 59643 := by
  apply descent_of_endpoint
  · rw [data_16_59643.1]; exact data_16_59643.2.2
  · rw [data_16_59643.2.1]; decide

end Collatz.Research.FirstDescent.Batch093
