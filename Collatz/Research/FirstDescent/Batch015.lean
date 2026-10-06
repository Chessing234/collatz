import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 15. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch015
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5615). -/
theorem data_13_5615 : oddCount 5615 13 = 8 ∧
    acceleratedOrbit 13 5615 = 4498 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5615 : ∀ j : Fin 13,
    5615 ≤ acceleratedOrbit j.val 5615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5615 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5615) = 6561 * m + 4498 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5615
  rw [data_13_5615.1, data_13_5615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5615 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5615) < 8192 * m + 5615 := by
  apply descent_of_endpoint
  · rw [data_13_5615.1]; exact data_13_5615.2.2
  · rw [data_13_5615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5723). -/
theorem data_13_5723 : oddCount 5723 13 = 8 ∧
    acceleratedOrbit 13 5723 = 4585 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5723 : ∀ j : Fin 13,
    5723 ≤ acceleratedOrbit j.val 5723 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5723 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5723) = 6561 * m + 4585 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5723
  rw [data_13_5723.1, data_13_5723.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5723 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5723) < 8192 * m + 5723 := by
  apply descent_of_endpoint
  · rw [data_13_5723.1]; exact data_13_5723.2.2
  · rw [data_13_5723.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5787). -/
theorem data_13_5787 : oddCount 5787 13 = 8 ∧
    acceleratedOrbit 13 5787 = 4636 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5787 : ∀ j : Fin 13,
    5787 ≤ acceleratedOrbit j.val 5787 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5787 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5787) = 6561 * m + 4636 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5787
  rw [data_13_5787.1, data_13_5787.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5787 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5787) < 8192 * m + 5787 := by
  apply descent_of_endpoint
  · rw [data_13_5787.1]; exact data_13_5787.2.2
  · rw [data_13_5787.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5871). -/
theorem data_13_5871 : oddCount 5871 13 = 8 ∧
    acceleratedOrbit 13 5871 = 4703 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5871 : ∀ j : Fin 13,
    5871 ≤ acceleratedOrbit j.val 5871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5871 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5871) = 6561 * m + 4703 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5871
  rw [data_13_5871.1, data_13_5871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5871 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5871) < 8192 * m + 5871 := by
  apply descent_of_endpoint
  · rw [data_13_5871.1]; exact data_13_5871.2.2
  · rw [data_13_5871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5959). -/
theorem data_13_5959 : oddCount 5959 13 = 8 ∧
    acceleratedOrbit 13 5959 = 4774 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5959 : ∀ j : Fin 13,
    5959 ≤ acceleratedOrbit j.val 5959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5959 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5959) = 6561 * m + 4774 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5959
  rw [data_13_5959.1, data_13_5959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5959 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5959) < 8192 * m + 5959 := by
  apply descent_of_endpoint
  · rw [data_13_5959.1]; exact data_13_5959.2.2
  · rw [data_13_5959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 5979). -/
theorem data_13_5979 : oddCount 5979 13 = 8 ∧
    acceleratedOrbit 13 5979 = 4790 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_5979 : ∀ j : Fin 13,
    5979 ≤ acceleratedOrbit j.val 5979 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_5979 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5979) = 6561 * m + 4790 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 5979
  rw [data_13_5979.1, data_13_5979.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_5979 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 5979) < 8192 * m + 5979 := by
  apply descent_of_endpoint
  · rw [data_13_5979.1]; exact data_13_5979.2.2
  · rw [data_13_5979.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6047). -/
theorem data_13_6047 : oddCount 6047 13 = 8 ∧
    acceleratedOrbit 13 6047 = 4844 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6047 : ∀ j : Fin 13,
    6047 ≤ acceleratedOrbit j.val 6047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6047 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6047) = 6561 * m + 4844 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6047
  rw [data_13_6047.1, data_13_6047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6047 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6047) < 8192 * m + 6047 := by
  apply descent_of_endpoint
  · rw [data_13_6047.1]; exact data_13_6047.2.2
  · rw [data_13_6047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 6215). -/
theorem data_13_6215 : oddCount 6215 13 = 8 ∧
    acceleratedOrbit 13 6215 = 4979 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_6215 : ∀ j : Fin 13,
    6215 ≤ acceleratedOrbit j.val 6215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_6215 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6215) = 6561 * m + 4979 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 6215
  rw [data_13_6215.1, data_13_6215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_6215 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 6215) < 8192 * m + 6215 := by
  apply descent_of_endpoint
  · rw [data_13_6215.1]; exact data_13_6215.2.2
  · rw [data_13_6215.2.1]; decide

end Collatz.Research.FirstDescent.Batch015
