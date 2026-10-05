import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 131. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch131
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 65695). -/
theorem data_18_65695 : oddCount 65695 18 = 11 ∧
    acceleratedOrbit 18 65695 = 44395 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_65695 : ∀ j : Fin 18,
    65695 ≤ acceleratedOrbit j.val 65695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_65695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 65695) = 177147 * m + 44395 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 65695
  rw [data_18_65695.1, data_18_65695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_65695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 65695) < 262144 * m + 65695 := by
  apply descent_of_endpoint
  · rw [data_18_65695.1]; exact data_18_65695.2.2
  · rw [data_18_65695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 66299). -/
theorem data_18_66299 : oddCount 66299 18 = 11 ∧
    acceleratedOrbit 18 66299 = 44804 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_66299 : ∀ j : Fin 18,
    66299 ≤ acceleratedOrbit j.val 66299 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_66299 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66299) = 177147 * m + 44804 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 66299
  rw [data_18_66299.1, data_18_66299.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_66299 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66299) < 262144 * m + 66299 := by
  apply descent_of_endpoint
  · rw [data_18_66299.1]; exact data_18_66299.2.2
  · rw [data_18_66299.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 66331). -/
theorem data_18_66331 : oddCount 66331 18 = 11 ∧
    acceleratedOrbit 18 66331 = 44825 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_66331 : ∀ j : Fin 18,
    66331 ≤ acceleratedOrbit j.val 66331 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_66331 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66331) = 177147 * m + 44825 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 66331
  rw [data_18_66331.1, data_18_66331.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_66331 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66331) < 262144 * m + 66331 := by
  apply descent_of_endpoint
  · rw [data_18_66331.1]; exact data_18_66331.2.2
  · rw [data_18_66331.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 66587). -/
theorem data_18_66587 : oddCount 66587 18 = 11 ∧
    acceleratedOrbit 18 66587 = 44998 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_66587 : ∀ j : Fin 18,
    66587 ≤ acceleratedOrbit j.val 66587 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_66587 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66587) = 177147 * m + 44998 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 66587
  rw [data_18_66587.1, data_18_66587.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_66587 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66587) < 262144 * m + 66587 := by
  apply descent_of_endpoint
  · rw [data_18_66587.1]; exact data_18_66587.2.2
  · rw [data_18_66587.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 66791). -/
theorem data_18_66791 : oddCount 66791 18 = 11 ∧
    acceleratedOrbit 18 66791 = 45136 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_66791 : ∀ j : Fin 18,
    66791 ≤ acceleratedOrbit j.val 66791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_66791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66791) = 177147 * m + 45136 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 66791
  rw [data_18_66791.1, data_18_66791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_66791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66791) < 262144 * m + 66791 := by
  apply descent_of_endpoint
  · rw [data_18_66791.1]; exact data_18_66791.2.2
  · rw [data_18_66791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 66975). -/
theorem data_18_66975 : oddCount 66975 18 = 11 ∧
    acceleratedOrbit 18 66975 = 45260 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_66975 : ∀ j : Fin 18,
    66975 ≤ acceleratedOrbit j.val 66975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_66975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66975) = 177147 * m + 45260 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 66975
  rw [data_18_66975.1, data_18_66975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_66975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 66975) < 262144 * m + 66975 := by
  apply descent_of_endpoint
  · rw [data_18_66975.1]; exact data_18_66975.2.2
  · rw [data_18_66975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 67023). -/
theorem data_18_67023 : oddCount 67023 18 = 11 ∧
    acceleratedOrbit 18 67023 = 45293 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_67023 : ∀ j : Fin 18,
    67023 ≤ acceleratedOrbit j.val 67023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_67023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67023) = 177147 * m + 45293 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 67023
  rw [data_18_67023.1, data_18_67023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_67023 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67023) < 262144 * m + 67023 := by
  apply descent_of_endpoint
  · rw [data_18_67023.1]; exact data_18_67023.2.2
  · rw [data_18_67023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 67231). -/
theorem data_18_67231 : oddCount 67231 18 = 11 ∧
    acceleratedOrbit 18 67231 = 45433 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_67231 : ∀ j : Fin 18,
    67231 ≤ acceleratedOrbit j.val 67231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_67231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67231) = 177147 * m + 45433 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 67231
  rw [data_18_67231.1, data_18_67231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_67231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 67231) < 262144 * m + 67231 := by
  apply descent_of_endpoint
  · rw [data_18_67231.1]; exact data_18_67231.2.2
  · rw [data_18_67231.2.1]; decide

end Collatz.Research.FirstDescent.Batch131
