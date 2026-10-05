import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 72. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch072
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 35311). -/
theorem data_16_35311 : oddCount 35311 16 = 10 ∧
    acceleratedOrbit 16 35311 = 31817 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_35311 : ∀ j : Fin 16,
    35311 ≤ acceleratedOrbit j.val 35311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_35311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35311) = 59049 * m + 31817 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 35311
  rw [data_16_35311.1, data_16_35311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_35311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35311) < 65536 * m + 35311 := by
  apply descent_of_endpoint
  · rw [data_16_35311.1]; exact data_16_35311.2.2
  · rw [data_16_35311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 35419). -/
theorem data_16_35419 : oddCount 35419 16 = 10 ∧
    acceleratedOrbit 16 35419 = 31915 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_35419 : ∀ j : Fin 16,
    35419 ≤ acceleratedOrbit j.val 35419 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_35419 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35419) = 59049 * m + 31915 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 35419
  rw [data_16_35419.1, data_16_35419.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_35419 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35419) < 65536 * m + 35419 := by
  apply descent_of_endpoint
  · rw [data_16_35419.1]; exact data_16_35419.2.2
  · rw [data_16_35419.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 35579). -/
theorem data_16_35579 : oddCount 35579 16 = 10 ∧
    acceleratedOrbit 16 35579 = 32059 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_35579 : ∀ j : Fin 16,
    35579 ≤ acceleratedOrbit j.val 35579 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_35579 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35579) = 59049 * m + 32059 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 35579
  rw [data_16_35579.1, data_16_35579.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_35579 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35579) < 65536 * m + 35579 := by
  apply descent_of_endpoint
  · rw [data_16_35579.1]; exact data_16_35579.2.2
  · rw [data_16_35579.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 35583). -/
theorem data_16_35583 : oddCount 35583 16 = 10 ∧
    acceleratedOrbit 16 35583 = 32062 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_35583 : ∀ j : Fin 16,
    35583 ≤ acceleratedOrbit j.val 35583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_35583 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35583) = 59049 * m + 32062 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 35583
  rw [data_16_35583.1, data_16_35583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_35583 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 35583) < 65536 * m + 35583 := by
  apply descent_of_endpoint
  · rw [data_16_35583.1]; exact data_16_35583.2.2
  · rw [data_16_35583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36143). -/
theorem data_16_36143 : oddCount 36143 16 = 10 ∧
    acceleratedOrbit 16 36143 = 32567 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36143 : ∀ j : Fin 16,
    36143 ≤ acceleratedOrbit j.val 36143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36143) = 59049 * m + 32567 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36143
  rw [data_16_36143.1, data_16_36143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36143) < 65536 * m + 36143 := by
  apply descent_of_endpoint
  · rw [data_16_36143.1]; exact data_16_36143.2.2
  · rw [data_16_36143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36159). -/
theorem data_16_36159 : oddCount 36159 16 = 10 ∧
    acceleratedOrbit 16 36159 = 32581 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36159 : ∀ j : Fin 16,
    36159 ≤ acceleratedOrbit j.val 36159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36159) = 59049 * m + 32581 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36159
  rw [data_16_36159.1, data_16_36159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36159) < 65536 * m + 36159 := by
  apply descent_of_endpoint
  · rw [data_16_36159.1]; exact data_16_36159.2.2
  · rw [data_16_36159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36383). -/
theorem data_16_36383 : oddCount 36383 16 = 10 ∧
    acceleratedOrbit 16 36383 = 32783 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36383 : ∀ j : Fin 16,
    36383 ≤ acceleratedOrbit j.val 36383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36383 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36383) = 59049 * m + 32783 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36383
  rw [data_16_36383.1, data_16_36383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36383 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36383) < 65536 * m + 36383 := by
  apply descent_of_endpoint
  · rw [data_16_36383.1]; exact data_16_36383.2.2
  · rw [data_16_36383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 36519). -/
theorem data_16_36519 : oddCount 36519 16 = 10 ∧
    acceleratedOrbit 16 36519 = 32906 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_36519 : ∀ j : Fin 16,
    36519 ≤ acceleratedOrbit j.val 36519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_36519 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36519) = 59049 * m + 32906 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 36519
  rw [data_16_36519.1, data_16_36519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_36519 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 36519) < 65536 * m + 36519 := by
  apply descent_of_endpoint
  · rw [data_16_36519.1]; exact data_16_36519.2.2
  · rw [data_16_36519.2.1]; decide

end Collatz.Research.FirstDescent.Batch072
