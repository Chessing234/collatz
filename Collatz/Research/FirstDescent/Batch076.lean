import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 76. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch076
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 39535). -/
theorem data_16_39535 : oddCount 39535 16 = 10 ∧
    acceleratedOrbit 16 39535 = 35623 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_39535 : ∀ j : Fin 16,
    39535 ≤ acceleratedOrbit j.val 39535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_39535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39535) = 59049 * m + 35623 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 39535
  rw [data_16_39535.1, data_16_39535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_39535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39535) < 65536 * m + 39535 := by
  apply descent_of_endpoint
  · rw [data_16_39535.1]; exact data_16_39535.2.2
  · rw [data_16_39535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 39615). -/
theorem data_16_39615 : oddCount 39615 16 = 10 ∧
    acceleratedOrbit 16 39615 = 35695 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_39615 : ∀ j : Fin 16,
    39615 ≤ acceleratedOrbit j.val 39615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_39615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39615) = 59049 * m + 35695 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 39615
  rw [data_16_39615.1, data_16_39615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_39615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39615) < 65536 * m + 39615 := by
  apply descent_of_endpoint
  · rw [data_16_39615.1]; exact data_16_39615.2.2
  · rw [data_16_39615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 39919). -/
theorem data_16_39919 : oddCount 39919 16 = 10 ∧
    acceleratedOrbit 16 39919 = 35969 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_39919 : ∀ j : Fin 16,
    39919 ≤ acceleratedOrbit j.val 39919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_39919 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39919) = 59049 * m + 35969 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 39919
  rw [data_16_39919.1, data_16_39919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_39919 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 39919) < 65536 * m + 39919 := by
  apply descent_of_endpoint
  · rw [data_16_39919.1]; exact data_16_39919.2.2
  · rw [data_16_39919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 40039). -/
theorem data_16_40039 : oddCount 40039 16 = 10 ∧
    acceleratedOrbit 16 40039 = 36077 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_40039 : ∀ j : Fin 16,
    40039 ≤ acceleratedOrbit j.val 40039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_40039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40039) = 59049 * m + 36077 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 40039
  rw [data_16_40039.1, data_16_40039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_40039 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40039) < 65536 * m + 40039 := by
  apply descent_of_endpoint
  · rw [data_16_40039.1]; exact data_16_40039.2.2
  · rw [data_16_40039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 40187). -/
theorem data_16_40187 : oddCount 40187 16 = 10 ∧
    acceleratedOrbit 16 40187 = 36211 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_40187 : ∀ j : Fin 16,
    40187 ≤ acceleratedOrbit j.val 40187 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_40187 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40187) = 59049 * m + 36211 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 40187
  rw [data_16_40187.1, data_16_40187.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_40187 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40187) < 65536 * m + 40187 := by
  apply descent_of_endpoint
  · rw [data_16_40187.1]; exact data_16_40187.2.2
  · rw [data_16_40187.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 40351). -/
theorem data_16_40351 : oddCount 40351 16 = 10 ∧
    acceleratedOrbit 16 40351 = 36358 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_40351 : ∀ j : Fin 16,
    40351 ≤ acceleratedOrbit j.val 40351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_40351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40351) = 59049 * m + 36358 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 40351
  rw [data_16_40351.1, data_16_40351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_40351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40351) < 65536 * m + 40351 := by
  apply descent_of_endpoint
  · rw [data_16_40351.1]; exact data_16_40351.2.2
  · rw [data_16_40351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 40415). -/
theorem data_16_40415 : oddCount 40415 16 = 10 ∧
    acceleratedOrbit 16 40415 = 36416 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_40415 : ∀ j : Fin 16,
    40415 ≤ acceleratedOrbit j.val 40415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_40415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40415) = 59049 * m + 36416 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 40415
  rw [data_16_40415.1, data_16_40415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_40415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40415) < 65536 * m + 40415 := by
  apply descent_of_endpoint
  · rw [data_16_40415.1]; exact data_16_40415.2.2
  · rw [data_16_40415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 40495). -/
theorem data_16_40495 : oddCount 40495 16 = 10 ∧
    acceleratedOrbit 16 40495 = 36488 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_40495 : ∀ j : Fin 16,
    40495 ≤ acceleratedOrbit j.val 40495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_40495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40495) = 59049 * m + 36488 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 40495
  rw [data_16_40495.1, data_16_40495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_40495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 40495) < 65536 * m + 40495 := by
  apply descent_of_endpoint
  · rw [data_16_40495.1]; exact data_16_40495.2.2
  · rw [data_16_40495.2.1]; decide

end Collatz.Research.FirstDescent.Batch076
