import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 250. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch250
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 83071). -/
theorem data_20_83071 : oddCount 83071 20 = 12 ∧
    acceleratedOrbit 20 83071 = 42103 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_83071 : ∀ j : Fin 20,
    83071 ≤ acceleratedOrbit j.val 83071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_83071 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83071) = 531441 * m + 42103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 83071
  rw [data_20_83071.1, data_20_83071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_83071 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83071) < 1048576 * m + 83071 := by
  apply descent_of_endpoint
  · rw [data_20_83071.1]; exact data_20_83071.2.2
  · rw [data_20_83071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 83227). -/
theorem data_20_83227 : oddCount 83227 20 = 12 ∧
    acceleratedOrbit 20 83227 = 42182 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_83227 : ∀ j : Fin 20,
    83227 ≤ acceleratedOrbit j.val 83227 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_83227 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83227) = 531441 * m + 42182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 83227
  rw [data_20_83227.1, data_20_83227.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_83227 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83227) < 1048576 * m + 83227 := by
  apply descent_of_endpoint
  · rw [data_20_83227.1]; exact data_20_83227.2.2
  · rw [data_20_83227.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 83611). -/
theorem data_20_83611 : oddCount 83611 20 = 12 ∧
    acceleratedOrbit 20 83611 = 42377 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_83611 : ∀ j : Fin 20,
    83611 ≤ acceleratedOrbit j.val 83611 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_83611 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83611) = 531441 * m + 42377 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 83611
  rw [data_20_83611.1, data_20_83611.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_83611 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 83611) < 1048576 * m + 83611 := by
  apply descent_of_endpoint
  · rw [data_20_83611.1]; exact data_20_83611.2.2
  · rw [data_20_83611.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 84415). -/
theorem data_20_84415 : oddCount 84415 20 = 12 ∧
    acceleratedOrbit 20 84415 = 42784 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_84415 : ∀ j : Fin 20,
    84415 ≤ acceleratedOrbit j.val 84415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_84415 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 84415) = 531441 * m + 42784 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 84415
  rw [data_20_84415.1, data_20_84415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_84415 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 84415) < 1048576 * m + 84415 := by
  apply descent_of_endpoint
  · rw [data_20_84415.1]; exact data_20_84415.2.2
  · rw [data_20_84415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 85103). -/
theorem data_20_85103 : oddCount 85103 20 = 12 ∧
    acceleratedOrbit 20 85103 = 43133 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_85103 : ∀ j : Fin 20,
    85103 ≤ acceleratedOrbit j.val 85103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_85103 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 85103) = 531441 * m + 43133 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 85103
  rw [data_20_85103.1, data_20_85103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_85103 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 85103) < 1048576 * m + 85103 := by
  apply descent_of_endpoint
  · rw [data_20_85103.1]; exact data_20_85103.2.2
  · rw [data_20_85103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 85671). -/
theorem data_20_85671 : oddCount 85671 20 = 12 ∧
    acceleratedOrbit 20 85671 = 43421 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_85671 : ∀ j : Fin 20,
    85671 ≤ acceleratedOrbit j.val 85671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_85671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 85671) = 531441 * m + 43421 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 85671
  rw [data_20_85671.1, data_20_85671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_85671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 85671) < 1048576 * m + 85671 := by
  apply descent_of_endpoint
  · rw [data_20_85671.1]; exact data_20_85671.2.2
  · rw [data_20_85671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 85711). -/
theorem data_20_85711 : oddCount 85711 20 = 12 ∧
    acceleratedOrbit 20 85711 = 43441 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_85711 : ∀ j : Fin 20,
    85711 ≤ acceleratedOrbit j.val 85711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_85711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 85711) = 531441 * m + 43441 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 85711
  rw [data_20_85711.1, data_20_85711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_85711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 85711) < 1048576 * m + 85711 := by
  apply descent_of_endpoint
  · rw [data_20_85711.1]; exact data_20_85711.2.2
  · rw [data_20_85711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 86107). -/
theorem data_20_86107 : oddCount 86107 20 = 12 ∧
    acceleratedOrbit 20 86107 = 43642 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_86107 : ∀ j : Fin 20,
    86107 ≤ acceleratedOrbit j.val 86107 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_86107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 86107) = 531441 * m + 43642 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 86107
  rw [data_20_86107.1, data_20_86107.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_86107 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 86107) < 1048576 * m + 86107 := by
  apply descent_of_endpoint
  · rw [data_20_86107.1]; exact data_20_86107.2.2
  · rw [data_20_86107.2.1]; decide

end Collatz.Research.FirstDescent.Batch250
