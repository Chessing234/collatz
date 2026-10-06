import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 90. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch090
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 55327). -/
theorem data_16_55327 : oddCount 55327 16 = 10 ∧
    acceleratedOrbit 16 55327 = 49852 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_55327 : ∀ j : Fin 16,
    55327 ≤ acceleratedOrbit j.val 55327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_55327 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55327) = 59049 * m + 49852 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 55327
  rw [data_16_55327.1, data_16_55327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_55327 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55327) < 65536 * m + 55327 := by
  apply descent_of_endpoint
  · rw [data_16_55327.1]; exact data_16_55327.2.2
  · rw [data_16_55327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 55407). -/
theorem data_16_55407 : oddCount 55407 16 = 10 ∧
    acceleratedOrbit 16 55407 = 49924 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_55407 : ∀ j : Fin 16,
    55407 ≤ acceleratedOrbit j.val 55407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_55407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55407) = 59049 * m + 49924 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 55407
  rw [data_16_55407.1, data_16_55407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_55407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55407) < 65536 * m + 55407 := by
  apply descent_of_endpoint
  · rw [data_16_55407.1]; exact data_16_55407.2.2
  · rw [data_16_55407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 55535). -/
theorem data_16_55535 : oddCount 55535 16 = 10 ∧
    acceleratedOrbit 16 55535 = 50039 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_55535 : ∀ j : Fin 16,
    55535 ≤ acceleratedOrbit j.val 55535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_55535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55535) = 59049 * m + 50039 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 55535
  rw [data_16_55535.1, data_16_55535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_55535 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55535) < 65536 * m + 55535 := by
  apply descent_of_endpoint
  · rw [data_16_55535.1]; exact data_16_55535.2.2
  · rw [data_16_55535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 55963). -/
theorem data_16_55963 : oddCount 55963 16 = 10 ∧
    acceleratedOrbit 16 55963 = 50425 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_55963 : ∀ j : Fin 16,
    55963 ≤ acceleratedOrbit j.val 55963 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_55963 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55963) = 59049 * m + 50425 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 55963
  rw [data_16_55963.1, data_16_55963.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_55963 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 55963) < 65536 * m + 55963 := by
  apply descent_of_endpoint
  · rw [data_16_55963.1]; exact data_16_55963.2.2
  · rw [data_16_55963.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 56059). -/
theorem data_16_56059 : oddCount 56059 16 = 10 ∧
    acceleratedOrbit 16 56059 = 50512 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_56059 : ∀ j : Fin 16,
    56059 ≤ acceleratedOrbit j.val 56059 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_56059 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56059) = 59049 * m + 50512 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 56059
  rw [data_16_56059.1, data_16_56059.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_56059 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56059) < 65536 * m + 56059 := by
  apply descent_of_endpoint
  · rw [data_16_56059.1]; exact data_16_56059.2.2
  · rw [data_16_56059.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 56191). -/
theorem data_16_56191 : oddCount 56191 16 = 10 ∧
    acceleratedOrbit 16 56191 = 50630 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_56191 : ∀ j : Fin 16,
    56191 ≤ acceleratedOrbit j.val 56191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_56191 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56191) = 59049 * m + 50630 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 56191
  rw [data_16_56191.1, data_16_56191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_56191 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56191) < 65536 * m + 56191 := by
  apply descent_of_endpoint
  · rw [data_16_56191.1]; exact data_16_56191.2.2
  · rw [data_16_56191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 56287). -/
theorem data_16_56287 : oddCount 56287 16 = 10 ∧
    acceleratedOrbit 16 56287 = 50717 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_56287 : ∀ j : Fin 16,
    56287 ≤ acceleratedOrbit j.val 56287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_56287 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56287) = 59049 * m + 50717 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 56287
  rw [data_16_56287.1, data_16_56287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_56287 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56287) < 65536 * m + 56287 := by
  apply descent_of_endpoint
  · rw [data_16_56287.1]; exact data_16_56287.2.2
  · rw [data_16_56287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 56315). -/
theorem data_16_56315 : oddCount 56315 16 = 10 ∧
    acceleratedOrbit 16 56315 = 50743 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_56315 : ∀ j : Fin 16,
    56315 ≤ acceleratedOrbit j.val 56315 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_56315 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56315) = 59049 * m + 50743 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 56315
  rw [data_16_56315.1, data_16_56315.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_56315 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 56315) < 65536 * m + 56315 := by
  apply descent_of_endpoint
  · rw [data_16_56315.1]; exact data_16_56315.2.2
  · rw [data_16_56315.2.1]; decide

end Collatz.Research.FirstDescent.Batch090
