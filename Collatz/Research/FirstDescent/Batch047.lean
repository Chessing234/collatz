import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 47. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch047
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7711). -/
theorem data_16_7711 : oddCount 7711 16 = 10 ∧
    acceleratedOrbit 16 7711 = 6949 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7711 : ∀ j : Fin 16,
    7711 ≤ acceleratedOrbit j.val 7711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7711 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7711) = 59049 * m + 6949 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7711
  rw [data_16_7711.1, data_16_7711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7711 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7711) < 65536 * m + 7711 := by
  apply descent_of_endpoint
  · rw [data_16_7711.1]; exact data_16_7711.2.2
  · rw [data_16_7711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7835). -/
theorem data_16_7835 : oddCount 7835 16 = 10 ∧
    acceleratedOrbit 16 7835 = 7061 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7835 : ∀ j : Fin 16,
    7835 ≤ acceleratedOrbit j.val 7835 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7835 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7835) = 59049 * m + 7061 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7835
  rw [data_16_7835.1, data_16_7835.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7835 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7835) < 65536 * m + 7835 := by
  apply descent_of_endpoint
  · rw [data_16_7835.1]; exact data_16_7835.2.2
  · rw [data_16_7835.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7871). -/
theorem data_16_7871 : oddCount 7871 16 = 10 ∧
    acceleratedOrbit 16 7871 = 7093 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7871 : ∀ j : Fin 16,
    7871 ≤ acceleratedOrbit j.val 7871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7871 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7871) = 59049 * m + 7093 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7871
  rw [data_16_7871.1, data_16_7871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7871 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7871) < 65536 * m + 7871 := by
  apply descent_of_endpoint
  · rw [data_16_7871.1]; exact data_16_7871.2.2
  · rw [data_16_7871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 7931). -/
theorem data_16_7931 : oddCount 7931 16 = 10 ∧
    acceleratedOrbit 16 7931 = 7148 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_7931 : ∀ j : Fin 16,
    7931 ≤ acceleratedOrbit j.val 7931 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_7931 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7931) = 59049 * m + 7148 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 7931
  rw [data_16_7931.1, data_16_7931.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_7931 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 7931) < 65536 * m + 7931 := by
  apply descent_of_endpoint
  · rw [data_16_7931.1]; exact data_16_7931.2.2
  · rw [data_16_7931.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 8095). -/
theorem data_16_8095 : oddCount 8095 16 = 10 ∧
    acceleratedOrbit 16 8095 = 7295 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_8095 : ∀ j : Fin 16,
    8095 ≤ acceleratedOrbit j.val 8095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_8095 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8095) = 59049 * m + 7295 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 8095
  rw [data_16_8095.1, data_16_8095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_8095 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8095) < 65536 * m + 8095 := by
  apply descent_of_endpoint
  · rw [data_16_8095.1]; exact data_16_8095.2.2
  · rw [data_16_8095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 8263). -/
theorem data_16_8263 : oddCount 8263 16 = 10 ∧
    acceleratedOrbit 16 8263 = 7447 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_8263 : ∀ j : Fin 16,
    8263 ≤ acceleratedOrbit j.val 8263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_8263 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8263) = 59049 * m + 7447 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 8263
  rw [data_16_8263.1, data_16_8263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_8263 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8263) < 65536 * m + 8263 := by
  apply descent_of_endpoint
  · rw [data_16_8263.1]; exact data_16_8263.2.2
  · rw [data_16_8263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 8551). -/
theorem data_16_8551 : oddCount 8551 16 = 10 ∧
    acceleratedOrbit 16 8551 = 7706 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_8551 : ∀ j : Fin 16,
    8551 ≤ acceleratedOrbit j.val 8551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_8551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8551) = 59049 * m + 7706 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 8551
  rw [data_16_8551.1, data_16_8551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_8551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8551) < 65536 * m + 8551 := by
  apply descent_of_endpoint
  · rw [data_16_8551.1]; exact data_16_8551.2.2
  · rw [data_16_8551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 8671). -/
theorem data_16_8671 : oddCount 8671 16 = 10 ∧
    acceleratedOrbit 16 8671 = 7814 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_8671 : ∀ j : Fin 16,
    8671 ≤ acceleratedOrbit j.val 8671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_8671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8671) = 59049 * m + 7814 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 8671
  rw [data_16_8671.1, data_16_8671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_8671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 8671) < 65536 * m + 8671 := by
  apply descent_of_endpoint
  · rw [data_16_8671.1]; exact data_16_8671.2.2
  · rw [data_16_8671.2.1]; decide

end Collatz.Research.FirstDescent.Batch047
