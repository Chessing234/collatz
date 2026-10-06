import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 163. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch163
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 133023). -/
theorem data_18_133023 : oddCount 133023 18 = 11 ∧
    acceleratedOrbit 18 133023 = 89893 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_133023 : ∀ j : Fin 18,
    133023 ≤ acceleratedOrbit j.val 133023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_133023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133023) = 177147 * m + 89893 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 133023
  rw [data_18_133023.1, data_18_133023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_133023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133023) < 262144 * m + 133023 := by
  apply descent_of_endpoint
  · rw [data_18_133023.1]; exact data_18_133023.2.2
  · rw [data_18_133023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 133535). -/
theorem data_18_133535 : oddCount 133535 18 = 11 ∧
    acceleratedOrbit 18 133535 = 90239 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_133535 : ∀ j : Fin 18,
    133535 ≤ acceleratedOrbit j.val 133535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_133535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133535) = 177147 * m + 90239 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 133535
  rw [data_18_133535.1, data_18_133535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_133535 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133535) < 262144 * m + 133535 := by
  apply descent_of_endpoint
  · rw [data_18_133535.1]; exact data_18_133535.2.2
  · rw [data_18_133535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 133583). -/
theorem data_18_133583 : oddCount 133583 18 = 11 ∧
    acceleratedOrbit 18 133583 = 90272 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_133583 : ∀ j : Fin 18,
    133583 ≤ acceleratedOrbit j.val 133583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_133583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133583) = 177147 * m + 90272 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 133583
  rw [data_18_133583.1, data_18_133583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_133583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133583) < 262144 * m + 133583 := by
  apply descent_of_endpoint
  · rw [data_18_133583.1]; exact data_18_133583.2.2
  · rw [data_18_133583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 133615). -/
theorem data_18_133615 : oddCount 133615 18 = 11 ∧
    acceleratedOrbit 18 133615 = 90293 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_133615 : ∀ j : Fin 18,
    133615 ≤ acceleratedOrbit j.val 133615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_133615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133615) = 177147 * m + 90293 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 133615
  rw [data_18_133615.1, data_18_133615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_133615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133615) < 262144 * m + 133615 := by
  apply descent_of_endpoint
  · rw [data_18_133615.1]; exact data_18_133615.2.2
  · rw [data_18_133615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 133951). -/
theorem data_18_133951 : oddCount 133951 18 = 11 ∧
    acceleratedOrbit 18 133951 = 90520 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_133951 : ∀ j : Fin 18,
    133951 ≤ acceleratedOrbit j.val 133951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_133951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133951) = 177147 * m + 90520 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 133951
  rw [data_18_133951.1, data_18_133951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_133951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133951) < 262144 * m + 133951 := by
  apply descent_of_endpoint
  · rw [data_18_133951.1]; exact data_18_133951.2.2
  · rw [data_18_133951.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 133991). -/
theorem data_18_133991 : oddCount 133991 18 = 11 ∧
    acceleratedOrbit 18 133991 = 90547 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_133991 : ∀ j : Fin 18,
    133991 ≤ acceleratedOrbit j.val 133991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_133991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133991) = 177147 * m + 90547 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 133991
  rw [data_18_133991.1, data_18_133991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_133991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 133991) < 262144 * m + 133991 := by
  apply descent_of_endpoint
  · rw [data_18_133991.1]; exact data_18_133991.2.2
  · rw [data_18_133991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 134271). -/
theorem data_18_134271 : oddCount 134271 18 = 11 ∧
    acceleratedOrbit 18 134271 = 90736 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_134271 : ∀ j : Fin 18,
    134271 ≤ acceleratedOrbit j.val 134271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_134271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 134271) = 177147 * m + 90736 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 134271
  rw [data_18_134271.1, data_18_134271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_134271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 134271) < 262144 * m + 134271 := by
  apply descent_of_endpoint
  · rw [data_18_134271.1]; exact data_18_134271.2.2
  · rw [data_18_134271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 134463). -/
theorem data_18_134463 : oddCount 134463 18 = 11 ∧
    acceleratedOrbit 18 134463 = 90866 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_134463 : ∀ j : Fin 18,
    134463 ≤ acceleratedOrbit j.val 134463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_134463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 134463) = 177147 * m + 90866 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 134463
  rw [data_18_134463.1, data_18_134463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_134463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 134463) < 262144 * m + 134463 := by
  apply descent_of_endpoint
  · rw [data_18_134463.1]; exact data_18_134463.2.2
  · rw [data_18_134463.2.1]; decide

end Collatz.Research.FirstDescent.Batch163
