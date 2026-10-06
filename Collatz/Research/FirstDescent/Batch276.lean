import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 276. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch276
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 171647). -/
theorem data_20_171647 : oddCount 171647 20 = 12 ∧
    acceleratedOrbit 20 171647 = 86995 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_171647 : ∀ j : Fin 20,
    171647 ≤ acceleratedOrbit j.val 171647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_171647 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 171647) = 531441 * m + 86995 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 171647
  rw [data_20_171647.1, data_20_171647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_171647 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 171647) < 1048576 * m + 171647 := by
  apply descent_of_endpoint
  · rw [data_20_171647.1]; exact data_20_171647.2.2
  · rw [data_20_171647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 171867). -/
theorem data_20_171867 : oddCount 171867 20 = 12 ∧
    acceleratedOrbit 20 171867 = 87107 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_171867 : ∀ j : Fin 20,
    171867 ≤ acceleratedOrbit j.val 171867 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_171867 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 171867) = 531441 * m + 87107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 171867
  rw [data_20_171867.1, data_20_171867.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_171867 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 171867) < 1048576 * m + 171867 := by
  apply descent_of_endpoint
  · rw [data_20_171867.1]; exact data_20_171867.2.2
  · rw [data_20_171867.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 172063). -/
theorem data_20_172063 : oddCount 172063 20 = 12 ∧
    acceleratedOrbit 20 172063 = 87206 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_172063 : ∀ j : Fin 20,
    172063 ≤ acceleratedOrbit j.val 172063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_172063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 172063) = 531441 * m + 87206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 172063
  rw [data_20_172063.1, data_20_172063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_172063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 172063) < 1048576 * m + 172063 := by
  apply descent_of_endpoint
  · rw [data_20_172063.1]; exact data_20_172063.2.2
  · rw [data_20_172063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 172671). -/
theorem data_20_172671 : oddCount 172671 20 = 12 ∧
    acceleratedOrbit 20 172671 = 87514 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_172671 : ∀ j : Fin 20,
    172671 ≤ acceleratedOrbit j.val 172671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_172671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 172671) = 531441 * m + 87514 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 172671
  rw [data_20_172671.1, data_20_172671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_172671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 172671) < 1048576 * m + 172671 := by
  apply descent_of_endpoint
  · rw [data_20_172671.1]; exact data_20_172671.2.2
  · rw [data_20_172671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 173039). -/
theorem data_20_173039 : oddCount 173039 20 = 12 ∧
    acceleratedOrbit 20 173039 = 87701 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_173039 : ∀ j : Fin 20,
    173039 ≤ acceleratedOrbit j.val 173039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_173039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 173039) = 531441 * m + 87701 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 173039
  rw [data_20_173039.1, data_20_173039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_173039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 173039) < 1048576 * m + 173039 := by
  apply descent_of_endpoint
  · rw [data_20_173039.1]; exact data_20_173039.2.2
  · rw [data_20_173039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 173087). -/
theorem data_20_173087 : oddCount 173087 20 = 12 ∧
    acceleratedOrbit 20 173087 = 87725 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_173087 : ∀ j : Fin 20,
    173087 ≤ acceleratedOrbit j.val 173087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_173087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 173087) = 531441 * m + 87725 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 173087
  rw [data_20_173087.1, data_20_173087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_173087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 173087) < 1048576 * m + 173087 := by
  apply descent_of_endpoint
  · rw [data_20_173087.1]; exact data_20_173087.2.2
  · rw [data_20_173087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 173807). -/
theorem data_20_173807 : oddCount 173807 20 = 12 ∧
    acceleratedOrbit 20 173807 = 88090 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_173807 : ∀ j : Fin 20,
    173807 ≤ acceleratedOrbit j.val 173807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_173807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 173807) = 531441 * m + 88090 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 173807
  rw [data_20_173807.1, data_20_173807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_173807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 173807) < 1048576 * m + 173807 := by
  apply descent_of_endpoint
  · rw [data_20_173807.1]; exact data_20_173807.2.2
  · rw [data_20_173807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 174247). -/
theorem data_20_174247 : oddCount 174247 20 = 12 ∧
    acceleratedOrbit 20 174247 = 88313 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_174247 : ∀ j : Fin 20,
    174247 ≤ acceleratedOrbit j.val 174247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_174247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 174247) = 531441 * m + 88313 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 174247
  rw [data_20_174247.1, data_20_174247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_174247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 174247) < 1048576 * m + 174247 := by
  apply descent_of_endpoint
  · rw [data_20_174247.1]; exact data_20_174247.2.2
  · rw [data_20_174247.2.1]; decide

end Collatz.Research.FirstDescent.Batch276
