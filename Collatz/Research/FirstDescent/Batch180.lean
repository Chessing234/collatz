import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 180. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch180
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 171167). -/
theorem data_18_171167 : oddCount 171167 18 = 11 ∧
    acceleratedOrbit 18 171167 = 115669 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_171167 : ∀ j : Fin 18,
    171167 ≤ acceleratedOrbit j.val 171167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_171167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171167) = 177147 * m + 115669 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 171167
  rw [data_18_171167.1, data_18_171167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_171167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171167) < 262144 * m + 171167 := by
  apply descent_of_endpoint
  · rw [data_18_171167.1]; exact data_18_171167.2.2
  · rw [data_18_171167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 171419). -/
theorem data_18_171419 : oddCount 171419 18 = 11 ∧
    acceleratedOrbit 18 171419 = 115840 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_171419 : ∀ j : Fin 18,
    171419 ≤ acceleratedOrbit j.val 171419 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_171419 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171419) = 177147 * m + 115840 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 171419
  rw [data_18_171419.1, data_18_171419.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_171419 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171419) < 262144 * m + 171419 := by
  apply descent_of_endpoint
  · rw [data_18_171419.1]; exact data_18_171419.2.2
  · rw [data_18_171419.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 171679). -/
theorem data_18_171679 : oddCount 171679 18 = 11 ∧
    acceleratedOrbit 18 171679 = 116015 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_171679 : ∀ j : Fin 18,
    171679 ≤ acceleratedOrbit j.val 171679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_171679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171679) = 177147 * m + 116015 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 171679
  rw [data_18_171679.1, data_18_171679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_171679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171679) < 262144 * m + 171679 := by
  apply descent_of_endpoint
  · rw [data_18_171679.1]; exact data_18_171679.2.2
  · rw [data_18_171679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 171771). -/
theorem data_18_171771 : oddCount 171771 18 = 11 ∧
    acceleratedOrbit 18 171771 = 116078 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_171771 : ∀ j : Fin 18,
    171771 ≤ acceleratedOrbit j.val 171771 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_171771 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171771) = 177147 * m + 116078 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 171771
  rw [data_18_171771.1, data_18_171771.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_171771 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 171771) < 262144 * m + 171771 := by
  apply descent_of_endpoint
  · rw [data_18_171771.1]; exact data_18_171771.2.2
  · rw [data_18_171771.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 172827). -/
theorem data_18_172827 : oddCount 172827 18 = 11 ∧
    acceleratedOrbit 18 172827 = 116791 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_172827 : ∀ j : Fin 18,
    172827 ≤ acceleratedOrbit j.val 172827 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_172827 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 172827) = 177147 * m + 116791 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 172827
  rw [data_18_172827.1, data_18_172827.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_172827 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 172827) < 262144 * m + 172827 := by
  apply descent_of_endpoint
  · rw [data_18_172827.1]; exact data_18_172827.2.2
  · rw [data_18_172827.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 172871). -/
theorem data_18_172871 : oddCount 172871 18 = 11 ∧
    acceleratedOrbit 18 172871 = 116821 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_172871 : ∀ j : Fin 18,
    172871 ≤ acceleratedOrbit j.val 172871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_172871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 172871) = 177147 * m + 116821 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 172871
  rw [data_18_172871.1, data_18_172871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_172871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 172871) < 262144 * m + 172871 := by
  apply descent_of_endpoint
  · rw [data_18_172871.1]; exact data_18_172871.2.2
  · rw [data_18_172871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 173295). -/
theorem data_18_173295 : oddCount 173295 18 = 11 ∧
    acceleratedOrbit 18 173295 = 117107 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_173295 : ∀ j : Fin 18,
    173295 ≤ acceleratedOrbit j.val 173295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_173295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173295) = 177147 * m + 117107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 173295
  rw [data_18_173295.1, data_18_173295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_173295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173295) < 262144 * m + 173295 := by
  apply descent_of_endpoint
  · rw [data_18_173295.1]; exact data_18_173295.2.2
  · rw [data_18_173295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 173383). -/
theorem data_18_173383 : oddCount 173383 18 = 11 ∧
    acceleratedOrbit 18 173383 = 117167 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_173383 : ∀ j : Fin 18,
    173383 ≤ acceleratedOrbit j.val 173383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_173383 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173383) = 177147 * m + 117167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 173383
  rw [data_18_173383.1, data_18_173383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_173383 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 173383) < 262144 * m + 173383 := by
  apply descent_of_endpoint
  · rw [data_18_173383.1]; exact data_18_173383.2.2
  · rw [data_18_173383.2.1]; decide

end Collatz.Research.FirstDescent.Batch180
