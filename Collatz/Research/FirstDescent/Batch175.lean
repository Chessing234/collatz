import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 175. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch175
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 161903). -/
theorem data_18_161903 : oddCount 161903 18 = 11 ∧
    acceleratedOrbit 18 161903 = 109409 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_161903 : ∀ j : Fin 18,
    161903 ≤ acceleratedOrbit j.val 161903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_161903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161903) = 177147 * m + 109409 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 161903
  rw [data_18_161903.1, data_18_161903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_161903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161903) < 262144 * m + 161903 := by
  apply descent_of_endpoint
  · rw [data_18_161903.1]; exact data_18_161903.2.2
  · rw [data_18_161903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 161999). -/
theorem data_18_161999 : oddCount 161999 18 = 11 ∧
    acceleratedOrbit 18 161999 = 109474 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_161999 : ∀ j : Fin 18,
    161999 ≤ acceleratedOrbit j.val 161999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_161999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161999) = 177147 * m + 109474 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 161999
  rw [data_18_161999.1, data_18_161999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_161999 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161999) < 262144 * m + 161999 := by
  apply descent_of_endpoint
  · rw [data_18_161999.1]; exact data_18_161999.2.2
  · rw [data_18_161999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162119). -/
theorem data_18_162119 : oddCount 162119 18 = 11 ∧
    acceleratedOrbit 18 162119 = 109555 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162119 : ∀ j : Fin 18,
    162119 ≤ acceleratedOrbit j.val 162119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162119) = 177147 * m + 109555 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162119
  rw [data_18_162119.1, data_18_162119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162119) < 262144 * m + 162119 := by
  apply descent_of_endpoint
  · rw [data_18_162119.1]; exact data_18_162119.2.2
  · rw [data_18_162119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162203). -/
theorem data_18_162203 : oddCount 162203 18 = 11 ∧
    acceleratedOrbit 18 162203 = 109612 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162203 : ∀ j : Fin 18,
    162203 ≤ acceleratedOrbit j.val 162203 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162203 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162203) = 177147 * m + 109612 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162203
  rw [data_18_162203.1, data_18_162203.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162203 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162203) < 262144 * m + 162203 := by
  apply descent_of_endpoint
  · rw [data_18_162203.1]; exact data_18_162203.2.2
  · rw [data_18_162203.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162351). -/
theorem data_18_162351 : oddCount 162351 18 = 11 ∧
    acceleratedOrbit 18 162351 = 109712 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162351 : ∀ j : Fin 18,
    162351 ≤ acceleratedOrbit j.val 162351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162351) = 177147 * m + 109712 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162351
  rw [data_18_162351.1, data_18_162351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162351) < 262144 * m + 162351 := by
  apply descent_of_endpoint
  · rw [data_18_162351.1]; exact data_18_162351.2.2
  · rw [data_18_162351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162471). -/
theorem data_18_162471 : oddCount 162471 18 = 11 ∧
    acceleratedOrbit 18 162471 = 109793 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162471 : ∀ j : Fin 18,
    162471 ≤ acceleratedOrbit j.val 162471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162471) = 177147 * m + 109793 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162471
  rw [data_18_162471.1, data_18_162471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162471) < 262144 * m + 162471 := by
  apply descent_of_endpoint
  · rw [data_18_162471.1]; exact data_18_162471.2.2
  · rw [data_18_162471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162511). -/
theorem data_18_162511 : oddCount 162511 18 = 11 ∧
    acceleratedOrbit 18 162511 = 109820 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162511 : ∀ j : Fin 18,
    162511 ≤ acceleratedOrbit j.val 162511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162511) = 177147 * m + 109820 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162511
  rw [data_18_162511.1, data_18_162511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162511) < 262144 * m + 162511 := by
  apply descent_of_endpoint
  · rw [data_18_162511.1]; exact data_18_162511.2.2
  · rw [data_18_162511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162555). -/
theorem data_18_162555 : oddCount 162555 18 = 11 ∧
    acceleratedOrbit 18 162555 = 109850 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162555 : ∀ j : Fin 18,
    162555 ≤ acceleratedOrbit j.val 162555 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162555) = 177147 * m + 109850 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162555
  rw [data_18_162555.1, data_18_162555.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162555) < 262144 * m + 162555 := by
  apply descent_of_endpoint
  · rw [data_18_162555.1]; exact data_18_162555.2.2
  · rw [data_18_162555.2.1]; decide

end Collatz.Research.FirstDescent.Batch175
