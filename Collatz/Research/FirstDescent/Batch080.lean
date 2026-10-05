import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 80. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch080
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43967). -/
theorem data_16_43967 : oddCount 43967 16 = 10 ∧
    acceleratedOrbit 16 43967 = 39616 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43967 : ∀ j : Fin 16,
    43967 ≤ acceleratedOrbit j.val 43967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43967 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43967) = 59049 * m + 39616 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43967
  rw [data_16_43967.1, data_16_43967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43967 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43967) < 65536 * m + 43967 := by
  apply descent_of_endpoint
  · rw [data_16_43967.1]; exact data_16_43967.2.2
  · rw [data_16_43967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 44143). -/
theorem data_16_44143 : oddCount 44143 16 = 10 ∧
    acceleratedOrbit 16 44143 = 39775 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_44143 : ∀ j : Fin 16,
    44143 ≤ acceleratedOrbit j.val 44143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_44143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44143) = 59049 * m + 39775 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 44143
  rw [data_16_44143.1, data_16_44143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_44143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44143) < 65536 * m + 44143 := by
  apply descent_of_endpoint
  · rw [data_16_44143.1]; exact data_16_44143.2.2
  · rw [data_16_44143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 44223). -/
theorem data_16_44223 : oddCount 44223 16 = 10 ∧
    acceleratedOrbit 16 44223 = 39847 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_44223 : ∀ j : Fin 16,
    44223 ≤ acceleratedOrbit j.val 44223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_44223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44223) = 59049 * m + 39847 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 44223
  rw [data_16_44223.1, data_16_44223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_44223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44223) < 65536 * m + 44223 := by
  apply descent_of_endpoint
  · rw [data_16_44223.1]; exact data_16_44223.2.2
  · rw [data_16_44223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 44239). -/
theorem data_16_44239 : oddCount 44239 16 = 10 ∧
    acceleratedOrbit 16 44239 = 39862 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_44239 : ∀ j : Fin 16,
    44239 ≤ acceleratedOrbit j.val 44239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_44239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44239) = 59049 * m + 39862 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 44239
  rw [data_16_44239.1, data_16_44239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_44239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44239) < 65536 * m + 44239 := by
  apply descent_of_endpoint
  · rw [data_16_44239.1]; exact data_16_44239.2.2
  · rw [data_16_44239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 44359). -/
theorem data_16_44359 : oddCount 44359 16 = 10 ∧
    acceleratedOrbit 16 44359 = 39970 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_44359 : ∀ j : Fin 16,
    44359 ≤ acceleratedOrbit j.val 44359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_44359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44359) = 59049 * m + 39970 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 44359
  rw [data_16_44359.1, data_16_44359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_44359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44359) < 65536 * m + 44359 := by
  apply descent_of_endpoint
  · rw [data_16_44359.1]; exact data_16_44359.2.2
  · rw [data_16_44359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 44699). -/
theorem data_16_44699 : oddCount 44699 16 = 10 ∧
    acceleratedOrbit 16 44699 = 40276 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_44699 : ∀ j : Fin 16,
    44699 ≤ acceleratedOrbit j.val 44699 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_44699 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44699) = 59049 * m + 40276 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 44699
  rw [data_16_44699.1, data_16_44699.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_44699 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44699) < 65536 * m + 44699 := by
  apply descent_of_endpoint
  · rw [data_16_44699.1]; exact data_16_44699.2.2
  · rw [data_16_44699.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 44959). -/
theorem data_16_44959 : oddCount 44959 16 = 10 ∧
    acceleratedOrbit 16 44959 = 40510 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_44959 : ∀ j : Fin 16,
    44959 ≤ acceleratedOrbit j.val 44959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_44959 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44959) = 59049 * m + 40510 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 44959
  rw [data_16_44959.1, data_16_44959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_44959 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 44959) < 65536 * m + 44959 := by
  apply descent_of_endpoint
  · rw [data_16_44959.1]; exact data_16_44959.2.2
  · rw [data_16_44959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45083). -/
theorem data_16_45083 : oddCount 45083 16 = 10 ∧
    acceleratedOrbit 16 45083 = 40622 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45083 : ∀ j : Fin 16,
    45083 ≤ acceleratedOrbit j.val 45083 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45083 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45083) = 59049 * m + 40622 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45083
  rw [data_16_45083.1, data_16_45083.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45083 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45083) < 65536 * m + 45083 := by
  apply descent_of_endpoint
  · rw [data_16_45083.1]; exact data_16_45083.2.2
  · rw [data_16_45083.2.1]; decide

end Collatz.Research.FirstDescent.Batch080
