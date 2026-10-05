import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 224. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch224
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 9063). -/
theorem data_20_9063 : oddCount 9063 20 = 12 ∧
    acceleratedOrbit 20 9063 = 4594 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_9063 : ∀ j : Fin 20,
    9063 ≤ acceleratedOrbit j.val 9063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_9063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9063) = 531441 * m + 4594 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 9063
  rw [data_20_9063.1, data_20_9063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_9063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9063) < 1048576 * m + 9063 := by
  apply descent_of_endpoint
  · rw [data_20_9063.1]; exact data_20_9063.2.2
  · rw [data_20_9063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 9343). -/
theorem data_20_9343 : oddCount 9343 20 = 12 ∧
    acceleratedOrbit 20 9343 = 4736 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_9343 : ∀ j : Fin 20,
    9343 ≤ acceleratedOrbit j.val 9343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_9343 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9343) = 531441 * m + 4736 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 9343
  rw [data_20_9343.1, data_20_9343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_9343 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9343) < 1048576 * m + 9343 := by
  apply descent_of_endpoint
  · rw [data_20_9343.1]; exact data_20_9343.2.2
  · rw [data_20_9343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 9447). -/
theorem data_20_9447 : oddCount 9447 20 = 12 ∧
    acceleratedOrbit 20 9447 = 4789 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_9447 : ∀ j : Fin 20,
    9447 ≤ acceleratedOrbit j.val 9447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_9447 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9447) = 531441 * m + 4789 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 9447
  rw [data_20_9447.1, data_20_9447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_9447 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9447) < 1048576 * m + 9447 := by
  apply descent_of_endpoint
  · rw [data_20_9447.1]; exact data_20_9447.2.2
  · rw [data_20_9447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 9703). -/
theorem data_20_9703 : oddCount 9703 20 = 12 ∧
    acceleratedOrbit 20 9703 = 4919 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_9703 : ∀ j : Fin 20,
    9703 ≤ acceleratedOrbit j.val 9703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_9703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9703) = 531441 * m + 4919 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 9703
  rw [data_20_9703.1, data_20_9703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_9703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 9703) < 1048576 * m + 9703 := by
  apply descent_of_endpoint
  · rw [data_20_9703.1]; exact data_20_9703.2.2
  · rw [data_20_9703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 10311). -/
theorem data_20_10311 : oddCount 10311 20 = 12 ∧
    acceleratedOrbit 20 10311 = 5227 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_10311 : ∀ j : Fin 20,
    10311 ≤ acceleratedOrbit j.val 10311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_10311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10311) = 531441 * m + 5227 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 10311
  rw [data_20_10311.1, data_20_10311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_10311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10311) < 1048576 * m + 10311 := by
  apply descent_of_endpoint
  · rw [data_20_10311.1]; exact data_20_10311.2.2
  · rw [data_20_10311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 10343). -/
theorem data_20_10343 : oddCount 10343 20 = 12 ∧
    acceleratedOrbit 20 10343 = 5243 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_10343 : ∀ j : Fin 20,
    10343 ≤ acceleratedOrbit j.val 10343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_10343 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10343) = 531441 * m + 5243 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 10343
  rw [data_20_10343.1, data_20_10343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_10343 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10343) < 1048576 * m + 10343 := by
  apply descent_of_endpoint
  · rw [data_20_10343.1]; exact data_20_10343.2.2
  · rw [data_20_10343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 10471). -/
theorem data_20_10471 : oddCount 10471 20 = 12 ∧
    acceleratedOrbit 20 10471 = 5308 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_10471 : ∀ j : Fin 20,
    10471 ≤ acceleratedOrbit j.val 10471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_10471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10471) = 531441 * m + 5308 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 10471
  rw [data_20_10471.1, data_20_10471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_10471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10471) < 1048576 * m + 10471 := by
  apply descent_of_endpoint
  · rw [data_20_10471.1]; exact data_20_10471.2.2
  · rw [data_20_10471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 10687). -/
theorem data_20_10687 : oddCount 10687 20 = 12 ∧
    acceleratedOrbit 20 10687 = 5417 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_10687 : ∀ j : Fin 20,
    10687 ≤ acceleratedOrbit j.val 10687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_10687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10687) = 531441 * m + 5417 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 10687
  rw [data_20_10687.1, data_20_10687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_10687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 10687) < 1048576 * m + 10687 := by
  apply descent_of_endpoint
  · rw [data_20_10687.1]; exact data_20_10687.2.2
  · rw [data_20_10687.2.1]; decide

end Collatz.Research.FirstDescent.Batch224
