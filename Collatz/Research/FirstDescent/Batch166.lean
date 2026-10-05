import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 166. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch166
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 140607). -/
theorem data_18_140607 : oddCount 140607 18 = 11 ∧
    acceleratedOrbit 18 140607 = 95018 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_140607 : ∀ j : Fin 18,
    140607 ≤ acceleratedOrbit j.val 140607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_140607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140607) = 177147 * m + 95018 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 140607
  rw [data_18_140607.1, data_18_140607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_140607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140607) < 262144 * m + 140607 := by
  apply descent_of_endpoint
  · rw [data_18_140607.1]; exact data_18_140607.2.2
  · rw [data_18_140607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 140647). -/
theorem data_18_140647 : oddCount 140647 18 = 11 ∧
    acceleratedOrbit 18 140647 = 95045 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_140647 : ∀ j : Fin 18,
    140647 ≤ acceleratedOrbit j.val 140647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_140647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140647) = 177147 * m + 95045 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 140647
  rw [data_18_140647.1, data_18_140647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_140647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140647) < 262144 * m + 140647 := by
  apply descent_of_endpoint
  · rw [data_18_140647.1]; exact data_18_140647.2.2
  · rw [data_18_140647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 140767). -/
theorem data_18_140767 : oddCount 140767 18 = 11 ∧
    acceleratedOrbit 18 140767 = 95126 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_140767 : ∀ j : Fin 18,
    140767 ≤ acceleratedOrbit j.val 140767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_140767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140767) = 177147 * m + 95126 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 140767
  rw [data_18_140767.1, data_18_140767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_140767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140767) < 262144 * m + 140767 := by
  apply descent_of_endpoint
  · rw [data_18_140767.1]; exact data_18_140767.2.2
  · rw [data_18_140767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 140775). -/
theorem data_18_140775 : oddCount 140775 18 = 11 ∧
    acceleratedOrbit 18 140775 = 95132 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_140775 : ∀ j : Fin 18,
    140775 ≤ acceleratedOrbit j.val 140775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_140775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140775) = 177147 * m + 95132 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 140775
  rw [data_18_140775.1, data_18_140775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_140775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140775) < 262144 * m + 140775 := by
  apply descent_of_endpoint
  · rw [data_18_140775.1]; exact data_18_140775.2.2
  · rw [data_18_140775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 140903). -/
theorem data_18_140903 : oddCount 140903 18 = 11 ∧
    acceleratedOrbit 18 140903 = 95218 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_140903 : ∀ j : Fin 18,
    140903 ≤ acceleratedOrbit j.val 140903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_140903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140903) = 177147 * m + 95218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 140903
  rw [data_18_140903.1, data_18_140903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_140903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140903) < 262144 * m + 140903 := by
  apply descent_of_endpoint
  · rw [data_18_140903.1]; exact data_18_140903.2.2
  · rw [data_18_140903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 141183). -/
theorem data_18_141183 : oddCount 141183 18 = 11 ∧
    acceleratedOrbit 18 141183 = 95407 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_141183 : ∀ j : Fin 18,
    141183 ≤ acceleratedOrbit j.val 141183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_141183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141183) = 177147 * m + 95407 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 141183
  rw [data_18_141183.1, data_18_141183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_141183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141183) < 262144 * m + 141183 := by
  apply descent_of_endpoint
  · rw [data_18_141183.1]; exact data_18_141183.2.2
  · rw [data_18_141183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 141215). -/
theorem data_18_141215 : oddCount 141215 18 = 11 ∧
    acceleratedOrbit 18 141215 = 95429 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_141215 : ∀ j : Fin 18,
    141215 ≤ acceleratedOrbit j.val 141215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_141215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141215) = 177147 * m + 95429 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 141215
  rw [data_18_141215.1, data_18_141215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_141215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141215) < 262144 * m + 141215 := by
  apply descent_of_endpoint
  · rw [data_18_141215.1]; exact data_18_141215.2.2
  · rw [data_18_141215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 141375). -/
theorem data_18_141375 : oddCount 141375 18 = 11 ∧
    acceleratedOrbit 18 141375 = 95537 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_141375 : ∀ j : Fin 18,
    141375 ≤ acceleratedOrbit j.val 141375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_141375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141375) = 177147 * m + 95537 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 141375
  rw [data_18_141375.1, data_18_141375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_141375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 141375) < 262144 * m + 141375 := by
  apply descent_of_endpoint
  · rw [data_18_141375.1]; exact data_18_141375.2.2
  · rw [data_18_141375.2.1]; decide

end Collatz.Research.FirstDescent.Batch166
