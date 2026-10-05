import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 135. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch135
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 71919). -/
theorem data_18_71919 : oddCount 71919 18 = 11 ∧
    acceleratedOrbit 18 71919 = 48601 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_71919 : ∀ j : Fin 18,
    71919 ≤ acceleratedOrbit j.val 71919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_71919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 71919) = 177147 * m + 48601 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 71919
  rw [data_18_71919.1, data_18_71919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_71919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 71919) < 262144 * m + 71919 := by
  apply descent_of_endpoint
  · rw [data_18_71919.1]; exact data_18_71919.2.2
  · rw [data_18_71919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 72431). -/
theorem data_18_72431 : oddCount 72431 18 = 11 ∧
    acceleratedOrbit 18 72431 = 48947 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_72431 : ∀ j : Fin 18,
    72431 ≤ acceleratedOrbit j.val 72431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_72431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 72431) = 177147 * m + 48947 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 72431
  rw [data_18_72431.1, data_18_72431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_72431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 72431) < 262144 * m + 72431 := by
  apply descent_of_endpoint
  · rw [data_18_72431.1]; exact data_18_72431.2.2
  · rw [data_18_72431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 72731). -/
theorem data_18_72731 : oddCount 72731 18 = 11 ∧
    acceleratedOrbit 18 72731 = 49150 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_72731 : ∀ j : Fin 18,
    72731 ≤ acceleratedOrbit j.val 72731 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_72731 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 72731) = 177147 * m + 49150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 72731
  rw [data_18_72731.1, data_18_72731.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_72731 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 72731) < 262144 * m + 72731 := by
  apply descent_of_endpoint
  · rw [data_18_72731.1]; exact data_18_72731.2.2
  · rw [data_18_72731.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 73119). -/
theorem data_18_73119 : oddCount 73119 18 = 11 ∧
    acceleratedOrbit 18 73119 = 49412 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_73119 : ∀ j : Fin 18,
    73119 ≤ acceleratedOrbit j.val 73119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_73119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 73119) = 177147 * m + 49412 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 73119
  rw [data_18_73119.1, data_18_73119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_73119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 73119) < 262144 * m + 73119 := by
  apply descent_of_endpoint
  · rw [data_18_73119.1]; exact data_18_73119.2.2
  · rw [data_18_73119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 73243). -/
theorem data_18_73243 : oddCount 73243 18 = 11 ∧
    acceleratedOrbit 18 73243 = 49496 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_73243 : ∀ j : Fin 18,
    73243 ≤ acceleratedOrbit j.val 73243 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_73243 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 73243) = 177147 * m + 49496 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 73243
  rw [data_18_73243.1, data_18_73243.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_73243 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 73243) < 262144 * m + 73243 := by
  apply descent_of_endpoint
  · rw [data_18_73243.1]; exact data_18_73243.2.2
  · rw [data_18_73243.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 74011). -/
theorem data_18_74011 : oddCount 74011 18 = 11 ∧
    acceleratedOrbit 18 74011 = 50015 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_74011 : ∀ j : Fin 18,
    74011 ≤ acceleratedOrbit j.val 74011 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_74011 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74011) = 177147 * m + 50015 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 74011
  rw [data_18_74011.1, data_18_74011.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_74011 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74011) < 262144 * m + 74011 := by
  apply descent_of_endpoint
  · rw [data_18_74011.1]; exact data_18_74011.2.2
  · rw [data_18_74011.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 74047). -/
theorem data_18_74047 : oddCount 74047 18 = 11 ∧
    acceleratedOrbit 18 74047 = 50039 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_74047 : ∀ j : Fin 18,
    74047 ≤ acceleratedOrbit j.val 74047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_74047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74047) = 177147 * m + 50039 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 74047
  rw [data_18_74047.1, data_18_74047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_74047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74047) < 262144 * m + 74047 := by
  apply descent_of_endpoint
  · rw [data_18_74047.1]; exact data_18_74047.2.2
  · rw [data_18_74047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 74143). -/
theorem data_18_74143 : oddCount 74143 18 = 11 ∧
    acceleratedOrbit 18 74143 = 50104 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_74143 : ∀ j : Fin 18,
    74143 ≤ acceleratedOrbit j.val 74143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_74143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74143) = 177147 * m + 50104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 74143
  rw [data_18_74143.1, data_18_74143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_74143 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74143) < 262144 * m + 74143 := by
  apply descent_of_endpoint
  · rw [data_18_74143.1]; exact data_18_74143.2.2
  · rw [data_18_74143.2.1]; decide

end Collatz.Research.FirstDescent.Batch135
