import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 125. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch125
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 55263). -/
theorem data_18_55263 : oddCount 55263 18 = 11 ∧
    acceleratedOrbit 18 55263 = 37346 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_55263 : ∀ j : Fin 18,
    55263 ≤ acceleratedOrbit j.val 55263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_55263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55263) = 177147 * m + 37346 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 55263
  rw [data_18_55263.1, data_18_55263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_55263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55263) < 262144 * m + 55263 := by
  apply descent_of_endpoint
  · rw [data_18_55263.1]; exact data_18_55263.2.2
  · rw [data_18_55263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 55343). -/
theorem data_18_55343 : oddCount 55343 18 = 11 ∧
    acceleratedOrbit 18 55343 = 37400 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_55343 : ∀ j : Fin 18,
    55343 ≤ acceleratedOrbit j.val 55343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_55343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55343) = 177147 * m + 37400 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 55343
  rw [data_18_55343.1, data_18_55343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_55343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55343) < 262144 * m + 55343 := by
  apply descent_of_endpoint
  · rw [data_18_55343.1]; exact data_18_55343.2.2
  · rw [data_18_55343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 55463). -/
theorem data_18_55463 : oddCount 55463 18 = 11 ∧
    acceleratedOrbit 18 55463 = 37481 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_55463 : ∀ j : Fin 18,
    55463 ≤ acceleratedOrbit j.val 55463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_55463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55463) = 177147 * m + 37481 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 55463
  rw [data_18_55463.1, data_18_55463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_55463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55463) < 262144 * m + 55463 := by
  apply descent_of_endpoint
  · rw [data_18_55463.1]; exact data_18_55463.2.2
  · rw [data_18_55463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 55503). -/
theorem data_18_55503 : oddCount 55503 18 = 11 ∧
    acceleratedOrbit 18 55503 = 37508 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_55503 : ∀ j : Fin 18,
    55503 ≤ acceleratedOrbit j.val 55503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_55503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55503) = 177147 * m + 37508 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 55503
  rw [data_18_55503.1, data_18_55503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_55503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55503) < 262144 * m + 55503 := by
  apply descent_of_endpoint
  · rw [data_18_55503.1]; exact data_18_55503.2.2
  · rw [data_18_55503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 55911). -/
theorem data_18_55911 : oddCount 55911 18 = 11 ∧
    acceleratedOrbit 18 55911 = 37784 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_55911 : ∀ j : Fin 18,
    55911 ≤ acceleratedOrbit j.val 55911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_55911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55911) = 177147 * m + 37784 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 55911
  rw [data_18_55911.1, data_18_55911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_55911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55911) < 262144 * m + 55911 := by
  apply descent_of_endpoint
  · rw [data_18_55911.1]; exact data_18_55911.2.2
  · rw [data_18_55911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 55919). -/
theorem data_18_55919 : oddCount 55919 18 = 11 ∧
    acceleratedOrbit 18 55919 = 37789 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_55919 : ∀ j : Fin 18,
    55919 ≤ acceleratedOrbit j.val 55919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_55919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55919) = 177147 * m + 37789 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 55919
  rw [data_18_55919.1, data_18_55919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_55919 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 55919) < 262144 * m + 55919 := by
  apply descent_of_endpoint
  · rw [data_18_55919.1]; exact data_18_55919.2.2
  · rw [data_18_55919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 56039). -/
theorem data_18_56039 : oddCount 56039 18 = 11 ∧
    acceleratedOrbit 18 56039 = 37870 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_56039 : ∀ j : Fin 18,
    56039 ≤ acceleratedOrbit j.val 56039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_56039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56039) = 177147 * m + 37870 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 56039
  rw [data_18_56039.1, data_18_56039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_56039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56039) < 262144 * m + 56039 := by
  apply descent_of_endpoint
  · rw [data_18_56039.1]; exact data_18_56039.2.2
  · rw [data_18_56039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 56063). -/
theorem data_18_56063 : oddCount 56063 18 = 11 ∧
    acceleratedOrbit 18 56063 = 37886 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_56063 : ∀ j : Fin 18,
    56063 ≤ acceleratedOrbit j.val 56063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_56063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56063) = 177147 * m + 37886 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 56063
  rw [data_18_56063.1, data_18_56063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_56063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 56063) < 262144 * m + 56063 := by
  apply descent_of_endpoint
  · rw [data_18_56063.1]; exact data_18_56063.2.2
  · rw [data_18_56063.2.1]; decide

end Collatz.Research.FirstDescent.Batch125
