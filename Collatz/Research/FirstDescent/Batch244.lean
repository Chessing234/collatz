import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 244. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch244
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 67687). -/
theorem data_20_67687 : oddCount 67687 20 = 12 ∧
    acceleratedOrbit 20 67687 = 34306 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_67687 : ∀ j : Fin 20,
    67687 ≤ acceleratedOrbit j.val 67687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_67687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 67687) = 531441 * m + 34306 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 67687
  rw [data_20_67687.1, data_20_67687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_67687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 67687) < 1048576 * m + 67687 := by
  apply descent_of_endpoint
  · rw [data_20_67687.1]; exact data_20_67687.2.2
  · rw [data_20_67687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 68047). -/
theorem data_20_68047 : oddCount 68047 20 = 12 ∧
    acceleratedOrbit 20 68047 = 34489 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_68047 : ∀ j : Fin 20,
    68047 ≤ acceleratedOrbit j.val 68047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_68047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68047) = 531441 * m + 34489 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 68047
  rw [data_20_68047.1, data_20_68047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_68047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68047) < 1048576 * m + 68047 := by
  apply descent_of_endpoint
  · rw [data_20_68047.1]; exact data_20_68047.2.2
  · rw [data_20_68047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 68251). -/
theorem data_20_68251 : oddCount 68251 20 = 12 ∧
    acceleratedOrbit 20 68251 = 34592 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_68251 : ∀ j : Fin 20,
    68251 ≤ acceleratedOrbit j.val 68251 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_68251 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68251) = 531441 * m + 34592 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 68251
  rw [data_20_68251.1, data_20_68251.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_68251 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68251) < 1048576 * m + 68251 := by
  apply descent_of_endpoint
  · rw [data_20_68251.1]; exact data_20_68251.2.2
  · rw [data_20_68251.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 68287). -/
theorem data_20_68287 : oddCount 68287 20 = 12 ∧
    acceleratedOrbit 20 68287 = 34610 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_68287 : ∀ j : Fin 20,
    68287 ≤ acceleratedOrbit j.val 68287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_68287 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68287) = 531441 * m + 34610 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 68287
  rw [data_20_68287.1, data_20_68287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_68287 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68287) < 1048576 * m + 68287 := by
  apply descent_of_endpoint
  · rw [data_20_68287.1]; exact data_20_68287.2.2
  · rw [data_20_68287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 68415). -/
theorem data_20_68415 : oddCount 68415 20 = 12 ∧
    acceleratedOrbit 20 68415 = 34675 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_68415 : ∀ j : Fin 20,
    68415 ≤ acceleratedOrbit j.val 68415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_68415 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68415) = 531441 * m + 34675 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 68415
  rw [data_20_68415.1, data_20_68415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_68415 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68415) < 1048576 * m + 68415 := by
  apply descent_of_endpoint
  · rw [data_20_68415.1]; exact data_20_68415.2.2
  · rw [data_20_68415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 68735). -/
theorem data_20_68735 : oddCount 68735 20 = 12 ∧
    acceleratedOrbit 20 68735 = 34837 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_68735 : ∀ j : Fin 20,
    68735 ≤ acceleratedOrbit j.val 68735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_68735 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68735) = 531441 * m + 34837 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 68735
  rw [data_20_68735.1, data_20_68735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_68735 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 68735) < 1048576 * m + 68735 := by
  apply descent_of_endpoint
  · rw [data_20_68735.1]; exact data_20_68735.2.2
  · rw [data_20_68735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 69631). -/
theorem data_20_69631 : oddCount 69631 20 = 12 ∧
    acceleratedOrbit 20 69631 = 35291 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_69631 : ∀ j : Fin 20,
    69631 ≤ acceleratedOrbit j.val 69631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_69631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 69631) = 531441 * m + 35291 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 69631
  rw [data_20_69631.1, data_20_69631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_69631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 69631) < 1048576 * m + 69631 := by
  apply descent_of_endpoint
  · rw [data_20_69631.1]; exact data_20_69631.2.2
  · rw [data_20_69631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 69743). -/
theorem data_20_69743 : oddCount 69743 20 = 12 ∧
    acceleratedOrbit 20 69743 = 35348 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_69743 : ∀ j : Fin 20,
    69743 ≤ acceleratedOrbit j.val 69743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_69743 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 69743) = 531441 * m + 35348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 69743
  rw [data_20_69743.1, data_20_69743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_69743 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 69743) < 1048576 * m + 69743 := by
  apply descent_of_endpoint
  · rw [data_20_69743.1]; exact data_20_69743.2.2
  · rw [data_20_69743.2.1]; decide

end Collatz.Research.FirstDescent.Batch244
