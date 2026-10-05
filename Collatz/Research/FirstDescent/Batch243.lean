import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 243. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch243
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 64615). -/
theorem data_20_64615 : oddCount 64615 20 = 12 ∧
    acceleratedOrbit 20 64615 = 32749 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_64615 : ∀ j : Fin 20,
    64615 ≤ acceleratedOrbit j.val 64615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_64615 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64615) = 531441 * m + 32749 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 64615
  rw [data_20_64615.1, data_20_64615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_64615 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64615) < 1048576 * m + 64615 := by
  apply descent_of_endpoint
  · rw [data_20_64615.1]; exact data_20_64615.2.2
  · rw [data_20_64615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 64895). -/
theorem data_20_64895 : oddCount 64895 20 = 12 ∧
    acceleratedOrbit 20 64895 = 32891 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_64895 : ∀ j : Fin 20,
    64895 ≤ acceleratedOrbit j.val 64895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_64895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64895) = 531441 * m + 32891 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 64895
  rw [data_20_64895.1, data_20_64895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_64895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 64895) < 1048576 * m + 64895 := by
  apply descent_of_endpoint
  · rw [data_20_64895.1]; exact data_20_64895.2.2
  · rw [data_20_64895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 65599). -/
theorem data_20_65599 : oddCount 65599 20 = 12 ∧
    acceleratedOrbit 20 65599 = 33248 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_65599 : ∀ j : Fin 20,
    65599 ≤ acceleratedOrbit j.val 65599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_65599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 65599) = 531441 * m + 33248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 65599
  rw [data_20_65599.1, data_20_65599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_65599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 65599) < 1048576 * m + 65599 := by
  apply descent_of_endpoint
  · rw [data_20_65599.1]; exact data_20_65599.2.2
  · rw [data_20_65599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 65647). -/
theorem data_20_65647 : oddCount 65647 20 = 12 ∧
    acceleratedOrbit 20 65647 = 33272 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_65647 : ∀ j : Fin 20,
    65647 ≤ acceleratedOrbit j.val 65647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_65647 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 65647) = 531441 * m + 33272 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 65647
  rw [data_20_65647.1, data_20_65647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_65647 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 65647) < 1048576 * m + 65647 := by
  apply descent_of_endpoint
  · rw [data_20_65647.1]; exact data_20_65647.2.2
  · rw [data_20_65647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 65775). -/
theorem data_20_65775 : oddCount 65775 20 = 12 ∧
    acceleratedOrbit 20 65775 = 33337 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_65775 : ∀ j : Fin 20,
    65775 ≤ acceleratedOrbit j.val 65775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_65775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 65775) = 531441 * m + 33337 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 65775
  rw [data_20_65775.1, data_20_65775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_65775 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 65775) < 1048576 * m + 65775 := by
  apply descent_of_endpoint
  · rw [data_20_65775.1]; exact data_20_65775.2.2
  · rw [data_20_65775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 66023). -/
theorem data_20_66023 : oddCount 66023 20 = 12 ∧
    acceleratedOrbit 20 66023 = 33463 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_66023 : ∀ j : Fin 20,
    66023 ≤ acceleratedOrbit j.val 66023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_66023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 66023) = 531441 * m + 33463 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 66023
  rw [data_20_66023.1, data_20_66023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_66023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 66023) < 1048576 * m + 66023 := by
  apply descent_of_endpoint
  · rw [data_20_66023.1]; exact data_20_66023.2.2
  · rw [data_20_66023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 66919). -/
theorem data_20_66919 : oddCount 66919 20 = 12 ∧
    acceleratedOrbit 20 66919 = 33917 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_66919 : ∀ j : Fin 20,
    66919 ≤ acceleratedOrbit j.val 66919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_66919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 66919) = 531441 * m + 33917 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 66919
  rw [data_20_66919.1, data_20_66919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_66919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 66919) < 1048576 * m + 66919 := by
  apply descent_of_endpoint
  · rw [data_20_66919.1]; exact data_20_66919.2.2
  · rw [data_20_66919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 67047). -/
theorem data_20_67047 : oddCount 67047 20 = 12 ∧
    acceleratedOrbit 20 67047 = 33982 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_67047 : ∀ j : Fin 20,
    67047 ≤ acceleratedOrbit j.val 67047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_67047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 67047) = 531441 * m + 33982 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 67047
  rw [data_20_67047.1, data_20_67047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_67047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 67047) < 1048576 * m + 67047 := by
  apply descent_of_endpoint
  · rw [data_20_67047.1]; exact data_20_67047.2.2
  · rw [data_20_67047.2.1]; decide

end Collatz.Research.FirstDescent.Batch243
