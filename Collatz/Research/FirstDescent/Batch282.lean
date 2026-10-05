import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 282. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch282
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 188463). -/
theorem data_20_188463 : oddCount 188463 20 = 12 ∧
    acceleratedOrbit 20 188463 = 95518 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_188463 : ∀ j : Fin 20,
    188463 ≤ acceleratedOrbit j.val 188463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_188463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 188463) = 531441 * m + 95518 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 188463
  rw [data_20_188463.1, data_20_188463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_188463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 188463) < 1048576 * m + 188463 := by
  apply descent_of_endpoint
  · rw [data_20_188463.1]; exact data_20_188463.2.2
  · rw [data_20_188463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 189767). -/
theorem data_20_189767 : oddCount 189767 20 = 12 ∧
    acceleratedOrbit 20 189767 = 96179 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_189767 : ∀ j : Fin 20,
    189767 ≤ acceleratedOrbit j.val 189767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_189767 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 189767) = 531441 * m + 96179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 189767
  rw [data_20_189767.1, data_20_189767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_189767 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 189767) < 1048576 * m + 189767 := by
  apply descent_of_endpoint
  · rw [data_20_189767.1]; exact data_20_189767.2.2
  · rw [data_20_189767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 190111). -/
theorem data_20_190111 : oddCount 190111 20 = 12 ∧
    acceleratedOrbit 20 190111 = 96353 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_190111 : ∀ j : Fin 20,
    190111 ≤ acceleratedOrbit j.val 190111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_190111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190111) = 531441 * m + 96353 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 190111
  rw [data_20_190111.1, data_20_190111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_190111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190111) < 1048576 * m + 190111 := by
  apply descent_of_endpoint
  · rw [data_20_190111.1]; exact data_20_190111.2.2
  · rw [data_20_190111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 190299). -/
theorem data_20_190299 : oddCount 190299 20 = 12 ∧
    acceleratedOrbit 20 190299 = 96449 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_190299 : ∀ j : Fin 20,
    190299 ≤ acceleratedOrbit j.val 190299 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_190299 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190299) = 531441 * m + 96449 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 190299
  rw [data_20_190299.1, data_20_190299.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_190299 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190299) < 1048576 * m + 190299 := by
  apply descent_of_endpoint
  · rw [data_20_190299.1]; exact data_20_190299.2.2
  · rw [data_20_190299.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 190459). -/
theorem data_20_190459 : oddCount 190459 20 = 12 ∧
    acceleratedOrbit 20 190459 = 96530 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_190459 : ∀ j : Fin 20,
    190459 ≤ acceleratedOrbit j.val 190459 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_190459 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190459) = 531441 * m + 96530 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 190459
  rw [data_20_190459.1, data_20_190459.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_190459 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190459) < 1048576 * m + 190459 := by
  apply descent_of_endpoint
  · rw [data_20_190459.1]; exact data_20_190459.2.2
  · rw [data_20_190459.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 190791). -/
theorem data_20_190791 : oddCount 190791 20 = 12 ∧
    acceleratedOrbit 20 190791 = 96698 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_190791 : ∀ j : Fin 20,
    190791 ≤ acceleratedOrbit j.val 190791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_190791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190791) = 531441 * m + 96698 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 190791
  rw [data_20_190791.1, data_20_190791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_190791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 190791) < 1048576 * m + 190791 := by
  apply descent_of_endpoint
  · rw [data_20_190791.1]; exact data_20_190791.2.2
  · rw [data_20_190791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 191067). -/
theorem data_20_191067 : oddCount 191067 20 = 12 ∧
    acceleratedOrbit 20 191067 = 96838 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_191067 : ∀ j : Fin 20,
    191067 ≤ acceleratedOrbit j.val 191067 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_191067 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191067) = 531441 * m + 96838 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 191067
  rw [data_20_191067.1, data_20_191067.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_191067 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191067) < 1048576 * m + 191067 := by
  apply descent_of_endpoint
  · rw [data_20_191067.1]; exact data_20_191067.2.2
  · rw [data_20_191067.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 191227). -/
theorem data_20_191227 : oddCount 191227 20 = 12 ∧
    acceleratedOrbit 20 191227 = 96919 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_191227 : ∀ j : Fin 20,
    191227 ≤ acceleratedOrbit j.val 191227 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_191227 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191227) = 531441 * m + 96919 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 191227
  rw [data_20_191227.1, data_20_191227.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_191227 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191227) < 1048576 * m + 191227 := by
  apply descent_of_endpoint
  · rw [data_20_191227.1]; exact data_20_191227.2.2
  · rw [data_20_191227.2.1]; decide

end Collatz.Research.FirstDescent.Batch282
