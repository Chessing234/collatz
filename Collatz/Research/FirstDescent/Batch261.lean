import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 261. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch261
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 120859). -/
theorem data_20_120859 : oddCount 120859 20 = 12 ∧
    acceleratedOrbit 20 120859 = 61255 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_120859 : ∀ j : Fin 20,
    120859 ≤ acceleratedOrbit j.val 120859 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_120859 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 120859) = 531441 * m + 61255 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 120859
  rw [data_20_120859.1, data_20_120859.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_120859 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 120859) < 1048576 * m + 120859 := by
  apply descent_of_endpoint
  · rw [data_20_120859.1]; exact data_20_120859.2.2
  · rw [data_20_120859.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 121471). -/
theorem data_20_121471 : oddCount 121471 20 = 12 ∧
    acceleratedOrbit 20 121471 = 61565 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_121471 : ∀ j : Fin 20,
    121471 ≤ acceleratedOrbit j.val 121471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_121471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 121471) = 531441 * m + 61565 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 121471
  rw [data_20_121471.1, data_20_121471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_121471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 121471) < 1048576 * m + 121471 := by
  apply descent_of_endpoint
  · rw [data_20_121471.1]; exact data_20_121471.2.2
  · rw [data_20_121471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 121791). -/
theorem data_20_121791 : oddCount 121791 20 = 12 ∧
    acceleratedOrbit 20 121791 = 61727 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_121791 : ∀ j : Fin 20,
    121791 ≤ acceleratedOrbit j.val 121791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_121791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 121791) = 531441 * m + 61727 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 121791
  rw [data_20_121791.1, data_20_121791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_121791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 121791) < 1048576 * m + 121791 := by
  apply descent_of_endpoint
  · rw [data_20_121791.1]; exact data_20_121791.2.2
  · rw [data_20_121791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 122335). -/
theorem data_20_122335 : oddCount 122335 20 = 12 ∧
    acceleratedOrbit 20 122335 = 62003 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_122335 : ∀ j : Fin 20,
    122335 ≤ acceleratedOrbit j.val 122335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_122335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 122335) = 531441 * m + 62003 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 122335
  rw [data_20_122335.1, data_20_122335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_122335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 122335) < 1048576 * m + 122335 := by
  apply descent_of_endpoint
  · rw [data_20_122335.1]; exact data_20_122335.2.2
  · rw [data_20_122335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 122351). -/
theorem data_20_122351 : oddCount 122351 20 = 12 ∧
    acceleratedOrbit 20 122351 = 62011 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_122351 : ∀ j : Fin 20,
    122351 ≤ acceleratedOrbit j.val 122351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_122351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 122351) = 531441 * m + 62011 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 122351
  rw [data_20_122351.1, data_20_122351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_122351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 122351) < 1048576 * m + 122351 := by
  apply descent_of_endpoint
  · rw [data_20_122351.1]; exact data_20_122351.2.2
  · rw [data_20_122351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 122927). -/
theorem data_20_122927 : oddCount 122927 20 = 12 ∧
    acceleratedOrbit 20 122927 = 62303 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_122927 : ∀ j : Fin 20,
    122927 ≤ acceleratedOrbit j.val 122927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_122927 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 122927) = 531441 * m + 62303 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 122927
  rw [data_20_122927.1, data_20_122927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_122927 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 122927) < 1048576 * m + 122927 := by
  apply descent_of_endpoint
  · rw [data_20_122927.1]; exact data_20_122927.2.2
  · rw [data_20_122927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 124263). -/
theorem data_20_124263 : oddCount 124263 20 = 12 ∧
    acceleratedOrbit 20 124263 = 62980 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_124263 : ∀ j : Fin 20,
    124263 ≤ acceleratedOrbit j.val 124263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_124263 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 124263) = 531441 * m + 62980 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 124263
  rw [data_20_124263.1, data_20_124263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_124263 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 124263) < 1048576 * m + 124263 := by
  apply descent_of_endpoint
  · rw [data_20_124263.1]; exact data_20_124263.2.2
  · rw [data_20_124263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 124507). -/
theorem data_20_124507 : oddCount 124507 20 = 12 ∧
    acceleratedOrbit 20 124507 = 63104 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_124507 : ∀ j : Fin 20,
    124507 ≤ acceleratedOrbit j.val 124507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_124507 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 124507) = 531441 * m + 63104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 124507
  rw [data_20_124507.1, data_20_124507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_124507 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 124507) < 1048576 * m + 124507 := by
  apply descent_of_endpoint
  · rw [data_20_124507.1]; exact data_20_124507.2.2
  · rw [data_20_124507.2.1]; decide

end Collatz.Research.FirstDescent.Batch261
