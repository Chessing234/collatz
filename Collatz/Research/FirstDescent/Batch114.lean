import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 114. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch114
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 30055). -/
theorem data_18_30055 : oddCount 30055 18 = 11 ∧
    acceleratedOrbit 18 30055 = 20311 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_30055 : ∀ j : Fin 18,
    30055 ≤ acceleratedOrbit j.val 30055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_30055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 30055) = 177147 * m + 20311 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 30055
  rw [data_18_30055.1, data_18_30055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_30055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 30055) < 262144 * m + 30055 := by
  apply descent_of_endpoint
  · rw [data_18_30055.1]; exact data_18_30055.2.2
  · rw [data_18_30055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 30335). -/
theorem data_18_30335 : oddCount 30335 18 = 11 ∧
    acceleratedOrbit 18 30335 = 20500 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_30335 : ∀ j : Fin 18,
    30335 ≤ acceleratedOrbit j.val 30335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_30335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 30335) = 177147 * m + 20500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 30335
  rw [data_18_30335.1, data_18_30335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_30335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 30335) < 262144 * m + 30335 := by
  apply descent_of_endpoint
  · rw [data_18_30335.1]; exact data_18_30335.2.2
  · rw [data_18_30335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 30567). -/
theorem data_18_30567 : oddCount 30567 18 = 11 ∧
    acceleratedOrbit 18 30567 = 20657 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_30567 : ∀ j : Fin 18,
    30567 ≤ acceleratedOrbit j.val 30567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_30567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 30567) = 177147 * m + 20657 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 30567
  rw [data_18_30567.1, data_18_30567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_30567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 30567) < 262144 * m + 30567 := by
  apply descent_of_endpoint
  · rw [data_18_30567.1]; exact data_18_30567.2.2
  · rw [data_18_30567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 31551). -/
theorem data_18_31551 : oddCount 31551 18 = 11 ∧
    acceleratedOrbit 18 31551 = 21322 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_31551 : ∀ j : Fin 18,
    31551 ≤ acceleratedOrbit j.val 31551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_31551 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31551) = 177147 * m + 21322 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 31551
  rw [data_18_31551.1, data_18_31551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_31551 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31551) < 262144 * m + 31551 := by
  apply descent_of_endpoint
  · rw [data_18_31551.1]; exact data_18_31551.2.2
  · rw [data_18_31551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 31591). -/
theorem data_18_31591 : oddCount 31591 18 = 11 ∧
    acceleratedOrbit 18 31591 = 21349 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_31591 : ∀ j : Fin 18,
    31591 ≤ acceleratedOrbit j.val 31591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_31591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31591) = 177147 * m + 21349 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 31591
  rw [data_18_31591.1, data_18_31591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_31591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31591) < 262144 * m + 31591 := by
  apply descent_of_endpoint
  · rw [data_18_31591.1]; exact data_18_31591.2.2
  · rw [data_18_31591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 31615). -/
theorem data_18_31615 : oddCount 31615 18 = 11 ∧
    acceleratedOrbit 18 31615 = 21365 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_31615 : ∀ j : Fin 18,
    31615 ≤ acceleratedOrbit j.val 31615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_31615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31615) = 177147 * m + 21365 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 31615
  rw [data_18_31615.1, data_18_31615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_31615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31615) < 262144 * m + 31615 := by
  apply descent_of_endpoint
  · rw [data_18_31615.1]; exact data_18_31615.2.2
  · rw [data_18_31615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 31871). -/
theorem data_18_31871 : oddCount 31871 18 = 11 ∧
    acceleratedOrbit 18 31871 = 21538 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_31871 : ∀ j : Fin 18,
    31871 ≤ acceleratedOrbit j.val 31871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_31871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31871) = 177147 * m + 21538 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 31871
  rw [data_18_31871.1, data_18_31871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_31871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 31871) < 262144 * m + 31871 := by
  apply descent_of_endpoint
  · rw [data_18_31871.1]; exact data_18_31871.2.2
  · rw [data_18_31871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 32063). -/
theorem data_18_32063 : oddCount 32063 18 = 11 ∧
    acceleratedOrbit 18 32063 = 21668 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_32063 : ∀ j : Fin 18,
    32063 ≤ acceleratedOrbit j.val 32063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_32063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 32063) = 177147 * m + 21668 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 32063
  rw [data_18_32063.1, data_18_32063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_32063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 32063) < 262144 * m + 32063 := by
  apply descent_of_endpoint
  · rw [data_18_32063.1]; exact data_18_32063.2.2
  · rw [data_18_32063.2.1]; decide

end Collatz.Research.FirstDescent.Batch114
