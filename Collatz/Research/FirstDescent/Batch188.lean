import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 188. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch188
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190191). -/
theorem data_18_190191 : oddCount 190191 18 = 11 ∧
    acceleratedOrbit 18 190191 = 128525 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190191 : ∀ j : Fin 18,
    190191 ≤ acceleratedOrbit j.val 190191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190191) = 177147 * m + 128525 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190191
  rw [data_18_190191.1, data_18_190191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190191) < 262144 * m + 190191 := by
  apply descent_of_endpoint
  · rw [data_18_190191.1]; exact data_18_190191.2.2
  · rw [data_18_190191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190279). -/
theorem data_18_190279 : oddCount 190279 18 = 11 ∧
    acceleratedOrbit 18 190279 = 128585 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190279 : ∀ j : Fin 18,
    190279 ≤ acceleratedOrbit j.val 190279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190279) = 177147 * m + 128585 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190279
  rw [data_18_190279.1, data_18_190279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190279 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190279) < 262144 * m + 190279 := by
  apply descent_of_endpoint
  · rw [data_18_190279.1]; exact data_18_190279.2.2
  · rw [data_18_190279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190527). -/
theorem data_18_190527 : oddCount 190527 18 = 11 ∧
    acceleratedOrbit 18 190527 = 128752 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190527 : ∀ j : Fin 18,
    190527 ≤ acceleratedOrbit j.val 190527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190527) = 177147 * m + 128752 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190527
  rw [data_18_190527.1, data_18_190527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190527) < 262144 * m + 190527 := by
  apply descent_of_endpoint
  · rw [data_18_190527.1]; exact data_18_190527.2.2
  · rw [data_18_190527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190555). -/
theorem data_18_190555 : oddCount 190555 18 = 11 ∧
    acceleratedOrbit 18 190555 = 128771 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190555 : ∀ j : Fin 18,
    190555 ≤ acceleratedOrbit j.val 190555 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190555) = 177147 * m + 128771 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190555
  rw [data_18_190555.1, data_18_190555.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190555 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190555) < 262144 * m + 190555 := by
  apply descent_of_endpoint
  · rw [data_18_190555.1]; exact data_18_190555.2.2
  · rw [data_18_190555.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190567). -/
theorem data_18_190567 : oddCount 190567 18 = 11 ∧
    acceleratedOrbit 18 190567 = 128779 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190567 : ∀ j : Fin 18,
    190567 ≤ acceleratedOrbit j.val 190567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190567) = 177147 * m + 128779 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190567
  rw [data_18_190567.1, data_18_190567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190567 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190567) < 262144 * m + 190567 := by
  apply descent_of_endpoint
  · rw [data_18_190567.1]; exact data_18_190567.2.2
  · rw [data_18_190567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190591). -/
theorem data_18_190591 : oddCount 190591 18 = 11 ∧
    acceleratedOrbit 18 190591 = 128795 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190591 : ∀ j : Fin 18,
    190591 ≤ acceleratedOrbit j.val 190591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190591) = 177147 * m + 128795 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190591
  rw [data_18_190591.1, data_18_190591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190591) < 262144 * m + 190591 := by
  apply descent_of_endpoint
  · rw [data_18_190591.1]; exact data_18_190591.2.2
  · rw [data_18_190591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190879). -/
theorem data_18_190879 : oddCount 190879 18 = 11 ∧
    acceleratedOrbit 18 190879 = 128990 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190879 : ∀ j : Fin 18,
    190879 ≤ acceleratedOrbit j.val 190879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190879) = 177147 * m + 128990 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190879
  rw [data_18_190879.1, data_18_190879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190879) < 262144 * m + 190879 := by
  apply descent_of_endpoint
  · rw [data_18_190879.1]; exact data_18_190879.2.2
  · rw [data_18_190879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 190959). -/
theorem data_18_190959 : oddCount 190959 18 = 11 ∧
    acceleratedOrbit 18 190959 = 129044 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_190959 : ∀ j : Fin 18,
    190959 ≤ acceleratedOrbit j.val 190959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_190959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190959) = 177147 * m + 129044 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 190959
  rw [data_18_190959.1, data_18_190959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_190959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 190959) < 262144 * m + 190959 := by
  apply descent_of_endpoint
  · rw [data_18_190959.1]; exact data_18_190959.2.2
  · rw [data_18_190959.2.1]; decide

end Collatz.Research.FirstDescent.Batch188
