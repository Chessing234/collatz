import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 157. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch157
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 119111). -/
theorem data_18_119111 : oddCount 119111 18 = 11 ∧
    acceleratedOrbit 18 119111 = 80492 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_119111 : ∀ j : Fin 18,
    119111 ≤ acceleratedOrbit j.val 119111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_119111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119111) = 177147 * m + 80492 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 119111
  rw [data_18_119111.1, data_18_119111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_119111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119111) < 262144 * m + 119111 := by
  apply descent_of_endpoint
  · rw [data_18_119111.1]; exact data_18_119111.2.2
  · rw [data_18_119111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 119271). -/
theorem data_18_119271 : oddCount 119271 18 = 11 ∧
    acceleratedOrbit 18 119271 = 80600 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_119271 : ∀ j : Fin 18,
    119271 ≤ acceleratedOrbit j.val 119271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_119271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119271) = 177147 * m + 80600 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 119271
  rw [data_18_119271.1, data_18_119271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_119271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119271) < 262144 * m + 119271 := by
  apply descent_of_endpoint
  · rw [data_18_119271.1]; exact data_18_119271.2.2
  · rw [data_18_119271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 119835). -/
theorem data_18_119835 : oddCount 119835 18 = 11 ∧
    acceleratedOrbit 18 119835 = 80981 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_119835 : ∀ j : Fin 18,
    119835 ≤ acceleratedOrbit j.val 119835 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_119835 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119835) = 177147 * m + 80981 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 119835
  rw [data_18_119835.1, data_18_119835.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_119835 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119835) < 262144 * m + 119835 := by
  apply descent_of_endpoint
  · rw [data_18_119835.1]; exact data_18_119835.2.2
  · rw [data_18_119835.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 119919). -/
theorem data_18_119919 : oddCount 119919 18 = 11 ∧
    acceleratedOrbit 18 119919 = 81038 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_119919 : ∀ j : Fin 18,
    119919 ≤ acceleratedOrbit j.val 119919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_119919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119919) = 177147 * m + 81038 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 119919
  rw [data_18_119919.1, data_18_119919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_119919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119919) < 262144 * m + 119919 := by
  apply descent_of_endpoint
  · rw [data_18_119919.1]; exact data_18_119919.2.2
  · rw [data_18_119919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 119967). -/
theorem data_18_119967 : oddCount 119967 18 = 11 ∧
    acceleratedOrbit 18 119967 = 81070 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_119967 : ∀ j : Fin 18,
    119967 ≤ acceleratedOrbit j.val 119967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_119967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119967) = 177147 * m + 81070 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 119967
  rw [data_18_119967.1, data_18_119967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_119967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119967) < 262144 * m + 119967 := by
  apply descent_of_endpoint
  · rw [data_18_119967.1]; exact data_18_119967.2.2
  · rw [data_18_119967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 119999). -/
theorem data_18_119999 : oddCount 119999 18 = 11 ∧
    acceleratedOrbit 18 119999 = 81092 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_119999 : ∀ j : Fin 18,
    119999 ≤ acceleratedOrbit j.val 119999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_119999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119999) = 177147 * m + 81092 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 119999
  rw [data_18_119999.1, data_18_119999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_119999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 119999) < 262144 * m + 119999 := by
  apply descent_of_endpoint
  · rw [data_18_119999.1]; exact data_18_119999.2.2
  · rw [data_18_119999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 120039). -/
theorem data_18_120039 : oddCount 120039 18 = 11 ∧
    acceleratedOrbit 18 120039 = 81119 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_120039 : ∀ j : Fin 18,
    120039 ≤ acceleratedOrbit j.val 120039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_120039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 120039) = 177147 * m + 81119 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 120039
  rw [data_18_120039.1, data_18_120039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_120039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 120039) < 262144 * m + 120039 := by
  apply descent_of_endpoint
  · rw [data_18_120039.1]; exact data_18_120039.2.2
  · rw [data_18_120039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 120091). -/
theorem data_18_120091 : oddCount 120091 18 = 11 ∧
    acceleratedOrbit 18 120091 = 81154 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_120091 : ∀ j : Fin 18,
    120091 ≤ acceleratedOrbit j.val 120091 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_120091 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 120091) = 177147 * m + 81154 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 120091
  rw [data_18_120091.1, data_18_120091.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_120091 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 120091) < 262144 * m + 120091 := by
  apply descent_of_endpoint
  · rw [data_18_120091.1]; exact data_18_120091.2.2
  · rw [data_18_120091.2.1]; decide

end Collatz.Research.FirstDescent.Batch157
