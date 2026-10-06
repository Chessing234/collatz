import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 265. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch265
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 136423). -/
theorem data_20_136423 : oddCount 136423 20 = 12 ∧
    acceleratedOrbit 20 136423 = 69143 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_136423 : ∀ j : Fin 20,
    136423 ≤ acceleratedOrbit j.val 136423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_136423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136423) = 531441 * m + 69143 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 136423
  rw [data_20_136423.1, data_20_136423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_136423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136423) < 1048576 * m + 136423 := by
  apply descent_of_endpoint
  · rw [data_20_136423.1]; exact data_20_136423.2.2
  · rw [data_20_136423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 136575). -/
theorem data_20_136575 : oddCount 136575 20 = 12 ∧
    acceleratedOrbit 20 136575 = 69220 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_136575 : ∀ j : Fin 20,
    136575 ≤ acceleratedOrbit j.val 136575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_136575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136575) = 531441 * m + 69220 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 136575
  rw [data_20_136575.1, data_20_136575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_136575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136575) < 1048576 * m + 136575 := by
  apply descent_of_endpoint
  · rw [data_20_136575.1]; exact data_20_136575.2.2
  · rw [data_20_136575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 136607). -/
theorem data_20_136607 : oddCount 136607 20 = 12 ∧
    acceleratedOrbit 20 136607 = 69236 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_136607 : ∀ j : Fin 20,
    136607 ≤ acceleratedOrbit j.val 136607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_136607 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136607) = 531441 * m + 69236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 136607
  rw [data_20_136607.1, data_20_136607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_136607 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 136607) < 1048576 * m + 136607 := by
  apply descent_of_endpoint
  · rw [data_20_136607.1]; exact data_20_136607.2.2
  · rw [data_20_136607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 137127). -/
theorem data_20_137127 : oddCount 137127 20 = 12 ∧
    acceleratedOrbit 20 137127 = 69500 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_137127 : ∀ j : Fin 20,
    137127 ≤ acceleratedOrbit j.val 137127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_137127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137127) = 531441 * m + 69500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 137127
  rw [data_20_137127.1, data_20_137127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_137127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137127) < 1048576 * m + 137127 := by
  apply descent_of_endpoint
  · rw [data_20_137127.1]; exact data_20_137127.2.2
  · rw [data_20_137127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 137151). -/
theorem data_20_137151 : oddCount 137151 20 = 12 ∧
    acceleratedOrbit 20 137151 = 69512 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_137151 : ∀ j : Fin 20,
    137151 ≤ acceleratedOrbit j.val 137151 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_137151 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137151) = 531441 * m + 69512 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 137151
  rw [data_20_137151.1, data_20_137151.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_137151 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137151) < 1048576 * m + 137151 := by
  apply descent_of_endpoint
  · rw [data_20_137151.1]; exact data_20_137151.2.2
  · rw [data_20_137151.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 137471). -/
theorem data_20_137471 : oddCount 137471 20 = 12 ∧
    acceleratedOrbit 20 137471 = 69674 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_137471 : ∀ j : Fin 20,
    137471 ≤ acceleratedOrbit j.val 137471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_137471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137471) = 531441 * m + 69674 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 137471
  rw [data_20_137471.1, data_20_137471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_137471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137471) < 1048576 * m + 137471 := by
  apply descent_of_endpoint
  · rw [data_20_137471.1]; exact data_20_137471.2.2
  · rw [data_20_137471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 137883). -/
theorem data_20_137883 : oddCount 137883 20 = 12 ∧
    acceleratedOrbit 20 137883 = 69883 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_137883 : ∀ j : Fin 20,
    137883 ≤ acceleratedOrbit j.val 137883 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_137883 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137883) = 531441 * m + 69883 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 137883
  rw [data_20_137883.1, data_20_137883.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_137883 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 137883) < 1048576 * m + 137883 := by
  apply descent_of_endpoint
  · rw [data_20_137883.1]; exact data_20_137883.2.2
  · rw [data_20_137883.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 139327). -/
theorem data_20_139327 : oddCount 139327 20 = 12 ∧
    acceleratedOrbit 20 139327 = 70615 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_139327 : ∀ j : Fin 20,
    139327 ≤ acceleratedOrbit j.val 139327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_139327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139327) = 531441 * m + 70615 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 139327
  rw [data_20_139327.1, data_20_139327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_139327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139327) < 1048576 * m + 139327 := by
  apply descent_of_endpoint
  · rw [data_20_139327.1]; exact data_20_139327.2.2
  · rw [data_20_139327.2.1]; decide

end Collatz.Research.FirstDescent.Batch265
