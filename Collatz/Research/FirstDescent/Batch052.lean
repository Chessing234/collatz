import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 52. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch052
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14015). -/
theorem data_16_14015 : oddCount 14015 16 = 10 ∧
    acceleratedOrbit 16 14015 = 12629 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14015 : ∀ j : Fin 16,
    14015 ≤ acceleratedOrbit j.val 14015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14015) = 59049 * m + 12629 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14015
  rw [data_16_14015.1, data_16_14015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14015) < 65536 * m + 14015 := by
  apply descent_of_endpoint
  · rw [data_16_14015.1]; exact data_16_14015.2.2
  · rw [data_16_14015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14207). -/
theorem data_16_14207 : oddCount 14207 16 = 10 ∧
    acceleratedOrbit 16 14207 = 12802 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14207 : ∀ j : Fin 16,
    14207 ≤ acceleratedOrbit j.val 14207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14207) = 59049 * m + 12802 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14207
  rw [data_16_14207.1, data_16_14207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14207) < 65536 * m + 14207 := by
  apply descent_of_endpoint
  · rw [data_16_14207.1]; exact data_16_14207.2.2
  · rw [data_16_14207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14303). -/
theorem data_16_14303 : oddCount 14303 16 = 10 ∧
    acceleratedOrbit 16 14303 = 12889 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14303 : ∀ j : Fin 16,
    14303 ≤ acceleratedOrbit j.val 14303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14303) = 59049 * m + 12889 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14303
  rw [data_16_14303.1, data_16_14303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14303 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14303) < 65536 * m + 14303 := by
  apply descent_of_endpoint
  · rw [data_16_14303.1]; exact data_16_14303.2.2
  · rw [data_16_14303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14363). -/
theorem data_16_14363 : oddCount 14363 16 = 10 ∧
    acceleratedOrbit 16 14363 = 12943 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14363 : ∀ j : Fin 16,
    14363 ≤ acceleratedOrbit j.val 14363 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14363 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14363) = 59049 * m + 12943 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14363
  rw [data_16_14363.1, data_16_14363.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14363 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14363) < 65536 * m + 14363 := by
  apply descent_of_endpoint
  · rw [data_16_14363.1]; exact data_16_14363.2.2
  · rw [data_16_14363.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14383). -/
theorem data_16_14383 : oddCount 14383 16 = 10 ∧
    acceleratedOrbit 16 14383 = 12961 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14383 : ∀ j : Fin 16,
    14383 ≤ acceleratedOrbit j.val 14383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14383 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14383) = 59049 * m + 12961 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14383
  rw [data_16_14383.1, data_16_14383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14383 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14383) < 65536 * m + 14383 := by
  apply descent_of_endpoint
  · rw [data_16_14383.1]; exact data_16_14383.2.2
  · rw [data_16_14383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14503). -/
theorem data_16_14503 : oddCount 14503 16 = 10 ∧
    acceleratedOrbit 16 14503 = 13069 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14503 : ∀ j : Fin 16,
    14503 ≤ acceleratedOrbit j.val 14503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14503 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14503) = 59049 * m + 13069 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14503
  rw [data_16_14503.1, data_16_14503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14503 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14503) < 65536 * m + 14503 := by
  apply descent_of_endpoint
  · rw [data_16_14503.1]; exact data_16_14503.2.2
  · rw [data_16_14503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14543). -/
theorem data_16_14543 : oddCount 14543 16 = 10 ∧
    acceleratedOrbit 16 14543 = 13105 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14543 : ∀ j : Fin 16,
    14543 ≤ acceleratedOrbit j.val 14543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14543 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14543) = 59049 * m + 13105 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14543
  rw [data_16_14543.1, data_16_14543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14543 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14543) < 65536 * m + 14543 := by
  apply descent_of_endpoint
  · rw [data_16_14543.1]; exact data_16_14543.2.2
  · rw [data_16_14543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 14747). -/
theorem data_16_14747 : oddCount 14747 16 = 10 ∧
    acceleratedOrbit 16 14747 = 13289 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_14747 : ∀ j : Fin 16,
    14747 ≤ acceleratedOrbit j.val 14747 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_14747 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14747) = 59049 * m + 13289 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 14747
  rw [data_16_14747.1, data_16_14747.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_14747 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 14747) < 65536 * m + 14747 := by
  apply descent_of_endpoint
  · rw [data_16_14747.1]; exact data_16_14747.2.2
  · rw [data_16_14747.2.1]; decide

end Collatz.Research.FirstDescent.Batch052
