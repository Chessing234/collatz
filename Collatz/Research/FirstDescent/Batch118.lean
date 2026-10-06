import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 118. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch118
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 41087). -/
theorem data_18_41087 : oddCount 41087 18 = 11 ∧
    acceleratedOrbit 18 41087 = 27766 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_41087 : ∀ j : Fin 18,
    41087 ≤ acceleratedOrbit j.val 41087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_41087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41087) = 177147 * m + 27766 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 41087
  rw [data_18_41087.1, data_18_41087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_41087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41087) < 262144 * m + 41087 := by
  apply descent_of_endpoint
  · rw [data_18_41087.1]; exact data_18_41087.2.2
  · rw [data_18_41087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 41319). -/
theorem data_18_41319 : oddCount 41319 18 = 11 ∧
    acceleratedOrbit 18 41319 = 27923 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_41319 : ∀ j : Fin 18,
    41319 ≤ acceleratedOrbit j.val 41319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_41319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41319) = 177147 * m + 27923 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 41319
  rw [data_18_41319.1, data_18_41319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_41319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41319) < 262144 * m + 41319 := by
  apply descent_of_endpoint
  · rw [data_18_41319.1]; exact data_18_41319.2.2
  · rw [data_18_41319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 41439). -/
theorem data_18_41439 : oddCount 41439 18 = 11 ∧
    acceleratedOrbit 18 41439 = 28004 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_41439 : ∀ j : Fin 18,
    41439 ≤ acceleratedOrbit j.val 41439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_41439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41439) = 177147 * m + 28004 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 41439
  rw [data_18_41439.1, data_18_41439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_41439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41439) < 262144 * m + 41439 := by
  apply descent_of_endpoint
  · rw [data_18_41439.1]; exact data_18_41439.2.2
  · rw [data_18_41439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 41519). -/
theorem data_18_41519 : oddCount 41519 18 = 11 ∧
    acceleratedOrbit 18 41519 = 28058 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_41519 : ∀ j : Fin 18,
    41519 ≤ acceleratedOrbit j.val 41519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_41519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41519) = 177147 * m + 28058 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 41519
  rw [data_18_41519.1, data_18_41519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_41519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41519) < 262144 * m + 41519 := by
  apply descent_of_endpoint
  · rw [data_18_41519.1]; exact data_18_41519.2.2
  · rw [data_18_41519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 41887). -/
theorem data_18_41887 : oddCount 41887 18 = 11 ∧
    acceleratedOrbit 18 41887 = 28307 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_41887 : ∀ j : Fin 18,
    41887 ≤ acceleratedOrbit j.val 41887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_41887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41887) = 177147 * m + 28307 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 41887
  rw [data_18_41887.1, data_18_41887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_41887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41887) < 262144 * m + 41887 := by
  apply descent_of_endpoint
  · rw [data_18_41887.1]; exact data_18_41887.2.2
  · rw [data_18_41887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 41967). -/
theorem data_18_41967 : oddCount 41967 18 = 11 ∧
    acceleratedOrbit 18 41967 = 28361 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_41967 : ∀ j : Fin 18,
    41967 ≤ acceleratedOrbit j.val 41967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_41967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41967) = 177147 * m + 28361 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 41967
  rw [data_18_41967.1, data_18_41967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_41967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 41967) < 262144 * m + 41967 := by
  apply descent_of_endpoint
  · rw [data_18_41967.1]; exact data_18_41967.2.2
  · rw [data_18_41967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 42015). -/
theorem data_18_42015 : oddCount 42015 18 = 11 ∧
    acceleratedOrbit 18 42015 = 28393 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_42015 : ∀ j : Fin 18,
    42015 ≤ acceleratedOrbit j.val 42015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_42015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 42015) = 177147 * m + 28393 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 42015
  rw [data_18_42015.1, data_18_42015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_42015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 42015) < 262144 * m + 42015 := by
  apply descent_of_endpoint
  · rw [data_18_42015.1]; exact data_18_42015.2.2
  · rw [data_18_42015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 42087). -/
theorem data_18_42087 : oddCount 42087 18 = 11 ∧
    acceleratedOrbit 18 42087 = 28442 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_42087 : ∀ j : Fin 18,
    42087 ≤ acceleratedOrbit j.val 42087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_42087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 42087) = 177147 * m + 28442 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 42087
  rw [data_18_42087.1, data_18_42087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_42087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 42087) < 262144 * m + 42087 := by
  apply descent_of_endpoint
  · rw [data_18_42087.1]; exact data_18_42087.2.2
  · rw [data_18_42087.2.1]; decide

end Collatz.Research.FirstDescent.Batch118
