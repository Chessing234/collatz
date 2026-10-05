import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 74. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch074
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37311). -/
theorem data_16_37311 : oddCount 37311 16 = 10 ∧
    acceleratedOrbit 16 37311 = 33619 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37311 : ∀ j : Fin 16,
    37311 ≤ acceleratedOrbit j.val 37311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37311) = 59049 * m + 33619 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37311
  rw [data_16_37311.1, data_16_37311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37311) < 65536 * m + 37311 := by
  apply descent_of_endpoint
  · rw [data_16_37311.1]; exact data_16_37311.2.2
  · rw [data_16_37311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37407). -/
theorem data_16_37407 : oddCount 37407 16 = 10 ∧
    acceleratedOrbit 16 37407 = 33706 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37407 : ∀ j : Fin 16,
    37407 ≤ acceleratedOrbit j.val 37407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37407) = 59049 * m + 33706 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37407
  rw [data_16_37407.1, data_16_37407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37407) < 65536 * m + 37407 := by
  apply descent_of_endpoint
  · rw [data_16_37407.1]; exact data_16_37407.2.2
  · rw [data_16_37407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37467). -/
theorem data_16_37467 : oddCount 37467 16 = 10 ∧
    acceleratedOrbit 16 37467 = 33760 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37467 : ∀ j : Fin 16,
    37467 ≤ acceleratedOrbit j.val 37467 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37467 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37467) = 59049 * m + 33760 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37467
  rw [data_16_37467.1, data_16_37467.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37467 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37467) < 65536 * m + 37467 := by
  apply descent_of_endpoint
  · rw [data_16_37467.1]; exact data_16_37467.2.2
  · rw [data_16_37467.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37487). -/
theorem data_16_37487 : oddCount 37487 16 = 10 ∧
    acceleratedOrbit 16 37487 = 33778 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37487 : ∀ j : Fin 16,
    37487 ≤ acceleratedOrbit j.val 37487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37487) = 59049 * m + 33778 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37487
  rw [data_16_37487.1, data_16_37487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37487) < 65536 * m + 37487 := by
  apply descent_of_endpoint
  · rw [data_16_37487.1]; exact data_16_37487.2.2
  · rw [data_16_37487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37607). -/
theorem data_16_37607 : oddCount 37607 16 = 10 ∧
    acceleratedOrbit 16 37607 = 33886 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37607 : ∀ j : Fin 16,
    37607 ≤ acceleratedOrbit j.val 37607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37607 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37607) = 59049 * m + 33886 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37607
  rw [data_16_37607.1, data_16_37607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37607 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37607) < 65536 * m + 37607 := by
  apply descent_of_endpoint
  · rw [data_16_37607.1]; exact data_16_37607.2.2
  · rw [data_16_37607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 37735). -/
theorem data_16_37735 : oddCount 37735 16 = 10 ∧
    acceleratedOrbit 16 37735 = 34001 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_37735 : ∀ j : Fin 16,
    37735 ≤ acceleratedOrbit j.val 37735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_37735 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37735) = 59049 * m + 34001 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 37735
  rw [data_16_37735.1, data_16_37735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_37735 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 37735) < 65536 * m + 37735 := by
  apply descent_of_endpoint
  · rw [data_16_37735.1]; exact data_16_37735.2.2
  · rw [data_16_37735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 38047). -/
theorem data_16_38047 : oddCount 38047 16 = 10 ∧
    acceleratedOrbit 16 38047 = 34282 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_38047 : ∀ j : Fin 16,
    38047 ≤ acceleratedOrbit j.val 38047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_38047 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38047) = 59049 * m + 34282 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 38047
  rw [data_16_38047.1, data_16_38047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_38047 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38047) < 65536 * m + 38047 := by
  apply descent_of_endpoint
  · rw [data_16_38047.1]; exact data_16_38047.2.2
  · rw [data_16_38047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 38171). -/
theorem data_16_38171 : oddCount 38171 16 = 10 ∧
    acceleratedOrbit 16 38171 = 34394 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_38171 : ∀ j : Fin 16,
    38171 ≤ acceleratedOrbit j.val 38171 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_38171 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38171) = 59049 * m + 34394 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 38171
  rw [data_16_38171.1, data_16_38171.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_38171 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 38171) < 65536 * m + 38171 := by
  apply descent_of_endpoint
  · rw [data_16_38171.1]; exact data_16_38171.2.2
  · rw [data_16_38171.2.1]; decide

end Collatz.Research.FirstDescent.Batch074
