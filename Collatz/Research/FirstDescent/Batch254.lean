import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 254. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch254
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 96667). -/
theorem data_20_96667 : oddCount 96667 20 = 12 ∧
    acceleratedOrbit 20 96667 = 48994 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_96667 : ∀ j : Fin 20,
    96667 ≤ acceleratedOrbit j.val 96667 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_96667 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96667) = 531441 * m + 48994 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 96667
  rw [data_20_96667.1, data_20_96667.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_96667 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96667) < 1048576 * m + 96667 := by
  apply descent_of_endpoint
  · rw [data_20_96667.1]; exact data_20_96667.2.2
  · rw [data_20_96667.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 96815). -/
theorem data_20_96815 : oddCount 96815 20 = 12 ∧
    acceleratedOrbit 20 96815 = 49069 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_96815 : ∀ j : Fin 20,
    96815 ≤ acceleratedOrbit j.val 96815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_96815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96815) = 531441 * m + 49069 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 96815
  rw [data_20_96815.1, data_20_96815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_96815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96815) < 1048576 * m + 96815 := by
  apply descent_of_endpoint
  · rw [data_20_96815.1]; exact data_20_96815.2.2
  · rw [data_20_96815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 96975). -/
theorem data_20_96975 : oddCount 96975 20 = 12 ∧
    acceleratedOrbit 20 96975 = 49150 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_96975 : ∀ j : Fin 20,
    96975 ≤ acceleratedOrbit j.val 96975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_96975 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96975) = 531441 * m + 49150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 96975
  rw [data_20_96975.1, data_20_96975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_96975 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96975) < 1048576 * m + 96975 := by
  apply descent_of_endpoint
  · rw [data_20_96975.1]; exact data_20_96975.2.2
  · rw [data_20_96975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 97023). -/
theorem data_20_97023 : oddCount 97023 20 = 12 ∧
    acceleratedOrbit 20 97023 = 49174 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_97023 : ∀ j : Fin 20,
    97023 ≤ acceleratedOrbit j.val 97023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_97023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 97023) = 531441 * m + 49174 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 97023
  rw [data_20_97023.1, data_20_97023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_97023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 97023) < 1048576 * m + 97023 := by
  apply descent_of_endpoint
  · rw [data_20_97023.1]; exact data_20_97023.2.2
  · rw [data_20_97023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 97563). -/
theorem data_20_97563 : oddCount 97563 20 = 12 ∧
    acceleratedOrbit 20 97563 = 49448 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_97563 : ∀ j : Fin 20,
    97563 ≤ acceleratedOrbit j.val 97563 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_97563 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 97563) = 531441 * m + 49448 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 97563
  rw [data_20_97563.1, data_20_97563.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_97563 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 97563) < 1048576 * m + 97563 := by
  apply descent_of_endpoint
  · rw [data_20_97563.1]; exact data_20_97563.2.2
  · rw [data_20_97563.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 97919). -/
theorem data_20_97919 : oddCount 97919 20 = 12 ∧
    acceleratedOrbit 20 97919 = 49628 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_97919 : ∀ j : Fin 20,
    97919 ≤ acceleratedOrbit j.val 97919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_97919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 97919) = 531441 * m + 49628 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 97919
  rw [data_20_97919.1, data_20_97919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_97919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 97919) < 1048576 * m + 97919 := by
  apply descent_of_endpoint
  · rw [data_20_97919.1]; exact data_20_97919.2.2
  · rw [data_20_97919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 98031). -/
theorem data_20_98031 : oddCount 98031 20 = 12 ∧
    acceleratedOrbit 20 98031 = 49685 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_98031 : ∀ j : Fin 20,
    98031 ≤ acceleratedOrbit j.val 98031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_98031 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 98031) = 531441 * m + 49685 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 98031
  rw [data_20_98031.1, data_20_98031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_98031 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 98031) < 1048576 * m + 98031 := by
  apply descent_of_endpoint
  · rw [data_20_98031.1]; exact data_20_98031.2.2
  · rw [data_20_98031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 98943). -/
theorem data_20_98943 : oddCount 98943 20 = 12 ∧
    acceleratedOrbit 20 98943 = 50147 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_98943 : ∀ j : Fin 20,
    98943 ≤ acceleratedOrbit j.val 98943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_98943 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 98943) = 531441 * m + 50147 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 98943
  rw [data_20_98943.1, data_20_98943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_98943 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 98943) < 1048576 * m + 98943 := by
  apply descent_of_endpoint
  · rw [data_20_98943.1]; exact data_20_98943.2.2
  · rw [data_20_98943.2.1]; decide

end Collatz.Research.FirstDescent.Batch254
