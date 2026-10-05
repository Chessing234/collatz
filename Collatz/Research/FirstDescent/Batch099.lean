import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 99. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch099
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 65179). -/
theorem data_16_65179 : oddCount 65179 16 = 10 ∧
    acceleratedOrbit 16 65179 = 58729 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_65179 : ∀ j : Fin 16,
    65179 ≤ acceleratedOrbit j.val 65179 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_65179 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65179) = 59049 * m + 58729 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 65179
  rw [data_16_65179.1, data_16_65179.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_65179 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65179) < 65536 * m + 65179 := by
  apply descent_of_endpoint
  · rw [data_16_65179.1]; exact data_16_65179.2.2
  · rw [data_16_65179.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 65183). -/
theorem data_16_65183 : oddCount 65183 16 = 10 ∧
    acceleratedOrbit 16 65183 = 58732 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_65183 : ∀ j : Fin 16,
    65183 ≤ acceleratedOrbit j.val 65183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_65183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65183) = 59049 * m + 58732 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 65183
  rw [data_16_65183.1, data_16_65183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_65183 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65183) < 65536 * m + 65183 := by
  apply descent_of_endpoint
  · rw [data_16_65183.1]; exact data_16_65183.2.2
  · rw [data_16_65183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 65275). -/
theorem data_16_65275 : oddCount 65275 16 = 10 ∧
    acceleratedOrbit 16 65275 = 58816 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_65275 : ∀ j : Fin 16,
    65275 ≤ acceleratedOrbit j.val 65275 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_65275 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65275) = 59049 * m + 58816 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 65275
  rw [data_16_65275.1, data_16_65275.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_65275 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65275) < 65536 * m + 65275 := by
  apply descent_of_endpoint
  · rw [data_16_65275.1]; exact data_16_65275.2.2
  · rw [data_16_65275.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 65407). -/
theorem data_16_65407 : oddCount 65407 16 = 10 ∧
    acceleratedOrbit 16 65407 = 58934 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_65407 : ∀ j : Fin 16,
    65407 ≤ acceleratedOrbit j.val 65407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_65407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65407) = 59049 * m + 58934 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 65407
  rw [data_16_65407.1, data_16_65407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_65407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65407) < 65536 * m + 65407 := by
  apply descent_of_endpoint
  · rw [data_16_65407.1]; exact data_16_65407.2.2
  · rw [data_16_65407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 65439). -/
theorem data_16_65439 : oddCount 65439 16 = 10 ∧
    acceleratedOrbit 16 65439 = 58963 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_65439 : ∀ j : Fin 16,
    65439 ≤ acceleratedOrbit j.val 65439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_65439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65439) = 59049 * m + 58963 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 65439
  rw [data_16_65439.1, data_16_65439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_65439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 65439) < 65536 * m + 65439 := by
  apply descent_of_endpoint
  · rw [data_16_65439.1]; exact data_16_65439.2.2
  · rw [data_16_65439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 511). -/
theorem data_18_511 : oddCount 511 18 = 11 ∧
    acceleratedOrbit 18 511 = 346 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_511 : ∀ j : Fin 18,
    511 ≤ acceleratedOrbit j.val 511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 511) = 177147 * m + 346 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 511
  rw [data_18_511.1, data_18_511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 511) < 262144 * m + 511 := by
  apply descent_of_endpoint
  · rw [data_18_511.1]; exact data_18_511.2.2
  · rw [data_18_511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 1023). -/
theorem data_18_1023 : oddCount 1023 18 = 11 ∧
    acceleratedOrbit 18 1023 = 692 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_1023 : ∀ j : Fin 18,
    1023 ≤ acceleratedOrbit j.val 1023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_1023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1023) = 177147 * m + 692 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 1023
  rw [data_18_1023.1, data_18_1023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_1023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1023) < 262144 * m + 1023 := by
  apply descent_of_endpoint
  · rw [data_18_1023.1]; exact data_18_1023.2.2
  · rw [data_18_1023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 1691). -/
theorem data_18_1691 : oddCount 1691 18 = 11 ∧
    acceleratedOrbit 18 1691 = 1144 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_1691 : ∀ j : Fin 18,
    1691 ≤ acceleratedOrbit j.val 1691 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_1691 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1691) = 177147 * m + 1144 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 1691
  rw [data_18_1691.1, data_18_1691.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_1691 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1691) < 262144 * m + 1691 := by
  apply descent_of_endpoint
  · rw [data_18_1691.1]; exact data_18_1691.2.2
  · rw [data_18_1691.2.1]; decide

end Collatz.Research.FirstDescent.Batch099
