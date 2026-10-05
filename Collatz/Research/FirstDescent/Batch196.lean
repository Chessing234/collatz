import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 196. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch196
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 210687). -/
theorem data_18_210687 : oddCount 210687 18 = 11 ∧
    acceleratedOrbit 18 210687 = 142375 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_210687 : ∀ j : Fin 18,
    210687 ≤ acceleratedOrbit j.val 210687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_210687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 210687) = 177147 * m + 142375 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 210687
  rw [data_18_210687.1, data_18_210687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_210687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 210687) < 262144 * m + 210687 := by
  apply descent_of_endpoint
  · rw [data_18_210687.1]; exact data_18_210687.2.2
  · rw [data_18_210687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 210975). -/
theorem data_18_210975 : oddCount 210975 18 = 11 ∧
    acceleratedOrbit 18 210975 = 142570 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_210975 : ∀ j : Fin 18,
    210975 ≤ acceleratedOrbit j.val 210975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_210975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 210975) = 177147 * m + 142570 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 210975
  rw [data_18_210975.1, data_18_210975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_210975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 210975) < 262144 * m + 210975 := by
  apply descent_of_endpoint
  · rw [data_18_210975.1]; exact data_18_210975.2.2
  · rw [data_18_210975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211055). -/
theorem data_18_211055 : oddCount 211055 18 = 11 ∧
    acceleratedOrbit 18 211055 = 142624 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211055 : ∀ j : Fin 18,
    211055 ≤ acceleratedOrbit j.val 211055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211055) = 177147 * m + 142624 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211055
  rw [data_18_211055.1, data_18_211055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211055) < 262144 * m + 211055 := by
  apply descent_of_endpoint
  · rw [data_18_211055.1]; exact data_18_211055.2.2
  · rw [data_18_211055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211167). -/
theorem data_18_211167 : oddCount 211167 18 = 11 ∧
    acceleratedOrbit 18 211167 = 142700 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211167 : ∀ j : Fin 18,
    211167 ≤ acceleratedOrbit j.val 211167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211167) = 177147 * m + 142700 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211167
  rw [data_18_211167.1, data_18_211167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211167) < 262144 * m + 211167 := by
  apply descent_of_endpoint
  · rw [data_18_211167.1]; exact data_18_211167.2.2
  · rw [data_18_211167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211327). -/
theorem data_18_211327 : oddCount 211327 18 = 11 ∧
    acceleratedOrbit 18 211327 = 142808 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211327 : ∀ j : Fin 18,
    211327 ≤ acceleratedOrbit j.val 211327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211327) = 177147 * m + 142808 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211327
  rw [data_18_211327.1, data_18_211327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211327) < 262144 * m + 211327 := by
  apply descent_of_endpoint
  · rw [data_18_211327.1]; exact data_18_211327.2.2
  · rw [data_18_211327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211567). -/
theorem data_18_211567 : oddCount 211567 18 = 11 ∧
    acceleratedOrbit 18 211567 = 142970 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211567 : ∀ j : Fin 18,
    211567 ≤ acceleratedOrbit j.val 211567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211567) = 177147 * m + 142970 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211567
  rw [data_18_211567.1, data_18_211567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211567) < 262144 * m + 211567 := by
  apply descent_of_endpoint
  · rw [data_18_211567.1]; exact data_18_211567.2.2
  · rw [data_18_211567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211623). -/
theorem data_18_211623 : oddCount 211623 18 = 11 ∧
    acceleratedOrbit 18 211623 = 143008 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211623 : ∀ j : Fin 18,
    211623 ≤ acceleratedOrbit j.val 211623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211623) = 177147 * m + 143008 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211623
  rw [data_18_211623.1, data_18_211623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211623) < 262144 * m + 211623 := by
  apply descent_of_endpoint
  · rw [data_18_211623.1]; exact data_18_211623.2.2
  · rw [data_18_211623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 211647). -/
theorem data_18_211647 : oddCount 211647 18 = 11 ∧
    acceleratedOrbit 18 211647 = 143024 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_211647 : ∀ j : Fin 18,
    211647 ≤ acceleratedOrbit j.val 211647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_211647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211647) = 177147 * m + 143024 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 211647
  rw [data_18_211647.1, data_18_211647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_211647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 211647) < 262144 * m + 211647 := by
  apply descent_of_endpoint
  · rw [data_18_211647.1]; exact data_18_211647.2.2
  · rw [data_18_211647.2.1]; decide

end Collatz.Research.FirstDescent.Batch196
