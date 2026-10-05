import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 147. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch147
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 101531). -/
theorem data_18_101531 : oddCount 101531 18 = 11 ∧
    acceleratedOrbit 18 101531 = 68612 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_101531 : ∀ j : Fin 18,
    101531 ≤ acceleratedOrbit j.val 101531 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_101531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101531) = 177147 * m + 68612 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 101531
  rw [data_18_101531.1, data_18_101531.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_101531 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101531) < 262144 * m + 101531 := by
  apply descent_of_endpoint
  · rw [data_18_101531.1]; exact data_18_101531.2.2
  · rw [data_18_101531.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 101627). -/
theorem data_18_101627 : oddCount 101627 18 = 11 ∧
    acceleratedOrbit 18 101627 = 68677 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_101627 : ∀ j : Fin 18,
    101627 ≤ acceleratedOrbit j.val 101627 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_101627 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101627) = 177147 * m + 68677 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 101627
  rw [data_18_101627.1, data_18_101627.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_101627 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 101627) < 262144 * m + 101627 := by
  apply descent_of_endpoint
  · rw [data_18_101627.1]; exact data_18_101627.2.2
  · rw [data_18_101627.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 102095). -/
theorem data_18_102095 : oddCount 102095 18 = 11 ∧
    acceleratedOrbit 18 102095 = 68993 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_102095 : ∀ j : Fin 18,
    102095 ≤ acceleratedOrbit j.val 102095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_102095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102095) = 177147 * m + 68993 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 102095
  rw [data_18_102095.1, data_18_102095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_102095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102095) < 262144 * m + 102095 := by
  apply descent_of_endpoint
  · rw [data_18_102095.1]; exact data_18_102095.2.2
  · rw [data_18_102095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 102431). -/
theorem data_18_102431 : oddCount 102431 18 = 11 ∧
    acceleratedOrbit 18 102431 = 69220 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_102431 : ∀ j : Fin 18,
    102431 ≤ acceleratedOrbit j.val 102431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_102431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102431) = 177147 * m + 69220 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 102431
  rw [data_18_102431.1, data_18_102431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_102431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102431) < 262144 * m + 102431 := by
  apply descent_of_endpoint
  · rw [data_18_102431.1]; exact data_18_102431.2.2
  · rw [data_18_102431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 102511). -/
theorem data_18_102511 : oddCount 102511 18 = 11 ∧
    acceleratedOrbit 18 102511 = 69274 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_102511 : ∀ j : Fin 18,
    102511 ≤ acceleratedOrbit j.val 102511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_102511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102511) = 177147 * m + 69274 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 102511
  rw [data_18_102511.1, data_18_102511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_102511 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102511) < 262144 * m + 102511 := by
  apply descent_of_endpoint
  · rw [data_18_102511.1]; exact data_18_102511.2.2
  · rw [data_18_102511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 102623). -/
theorem data_18_102623 : oddCount 102623 18 = 11 ∧
    acceleratedOrbit 18 102623 = 69350 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_102623 : ∀ j : Fin 18,
    102623 ≤ acceleratedOrbit j.val 102623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_102623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102623) = 177147 * m + 69350 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 102623
  rw [data_18_102623.1, data_18_102623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_102623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 102623) < 262144 * m + 102623 := by
  apply descent_of_endpoint
  · rw [data_18_102623.1]; exact data_18_102623.2.2
  · rw [data_18_102623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 103103). -/
theorem data_18_103103 : oddCount 103103 18 = 11 ∧
    acceleratedOrbit 18 103103 = 69674 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_103103 : ∀ j : Fin 18,
    103103 ≤ acceleratedOrbit j.val 103103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_103103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 103103) = 177147 * m + 69674 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 103103
  rw [data_18_103103.1, data_18_103103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_103103 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 103103) < 262144 * m + 103103 := by
  apply descent_of_endpoint
  · rw [data_18_103103.1]; exact data_18_103103.2.2
  · rw [data_18_103103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 103391). -/
theorem data_18_103391 : oddCount 103391 18 = 11 ∧
    acceleratedOrbit 18 103391 = 69869 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_103391 : ∀ j : Fin 18,
    103391 ≤ acceleratedOrbit j.val 103391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_103391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 103391) = 177147 * m + 69869 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 103391
  rw [data_18_103391.1, data_18_103391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_103391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 103391) < 262144 * m + 103391 := by
  apply descent_of_endpoint
  · rw [data_18_103391.1]; exact data_18_103391.2.2
  · rw [data_18_103391.2.1]; decide

end Collatz.Research.FirstDescent.Batch147
