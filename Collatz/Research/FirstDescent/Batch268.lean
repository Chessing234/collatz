import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 268. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch268
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 144799). -/
theorem data_20_144799 : oddCount 144799 20 = 12 ∧
    acceleratedOrbit 20 144799 = 73388 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_144799 : ∀ j : Fin 20,
    144799 ≤ acceleratedOrbit j.val 144799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_144799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 144799) = 531441 * m + 73388 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 144799
  rw [data_20_144799.1, data_20_144799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_144799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 144799) < 1048576 * m + 144799 := by
  apply descent_of_endpoint
  · rw [data_20_144799.1]; exact data_20_144799.2.2
  · rw [data_20_144799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 145519). -/
theorem data_20_145519 : oddCount 145519 20 = 12 ∧
    acceleratedOrbit 20 145519 = 73753 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_145519 : ∀ j : Fin 20,
    145519 ≤ acceleratedOrbit j.val 145519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_145519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 145519) = 531441 * m + 73753 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 145519
  rw [data_20_145519.1, data_20_145519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_145519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 145519) < 1048576 * m + 145519 := by
  apply descent_of_endpoint
  · rw [data_20_145519.1]; exact data_20_145519.2.2
  · rw [data_20_145519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 145631). -/
theorem data_20_145631 : oddCount 145631 20 = 12 ∧
    acceleratedOrbit 20 145631 = 73810 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_145631 : ∀ j : Fin 20,
    145631 ≤ acceleratedOrbit j.val 145631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_145631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 145631) = 531441 * m + 73810 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 145631
  rw [data_20_145631.1, data_20_145631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_145631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 145631) < 1048576 * m + 145631 := by
  apply descent_of_endpoint
  · rw [data_20_145631.1]; exact data_20_145631.2.2
  · rw [data_20_145631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 145791). -/
theorem data_20_145791 : oddCount 145791 20 = 12 ∧
    acceleratedOrbit 20 145791 = 73891 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_145791 : ∀ j : Fin 20,
    145791 ≤ acceleratedOrbit j.val 145791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_145791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 145791) = 531441 * m + 73891 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 145791
  rw [data_20_145791.1, data_20_145791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_145791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 145791) < 1048576 * m + 145791 := by
  apply descent_of_endpoint
  · rw [data_20_145791.1]; exact data_20_145791.2.2
  · rw [data_20_145791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 146087). -/
theorem data_20_146087 : oddCount 146087 20 = 12 ∧
    acceleratedOrbit 20 146087 = 74041 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_146087 : ∀ j : Fin 20,
    146087 ≤ acceleratedOrbit j.val 146087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_146087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146087) = 531441 * m + 74041 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 146087
  rw [data_20_146087.1, data_20_146087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_146087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146087) < 1048576 * m + 146087 := by
  apply descent_of_endpoint
  · rw [data_20_146087.1]; exact data_20_146087.2.2
  · rw [data_20_146087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 146111). -/
theorem data_20_146111 : oddCount 146111 20 = 12 ∧
    acceleratedOrbit 20 146111 = 74053 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_146111 : ∀ j : Fin 20,
    146111 ≤ acceleratedOrbit j.val 146111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_146111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146111) = 531441 * m + 74053 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 146111
  rw [data_20_146111.1, data_20_146111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_146111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146111) < 1048576 * m + 146111 := by
  apply descent_of_endpoint
  · rw [data_20_146111.1]; exact data_20_146111.2.2
  · rw [data_20_146111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 146847). -/
theorem data_20_146847 : oddCount 146847 20 = 12 ∧
    acceleratedOrbit 20 146847 = 74426 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_146847 : ∀ j : Fin 20,
    146847 ≤ acceleratedOrbit j.val 146847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_146847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146847) = 531441 * m + 74426 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 146847
  rw [data_20_146847.1, data_20_146847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_146847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146847) < 1048576 * m + 146847 := by
  apply descent_of_endpoint
  · rw [data_20_146847.1]; exact data_20_146847.2.2
  · rw [data_20_146847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 146971). -/
theorem data_20_146971 : oddCount 146971 20 = 12 ∧
    acceleratedOrbit 20 146971 = 74489 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_146971 : ∀ j : Fin 20,
    146971 ≤ acceleratedOrbit j.val 146971 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_146971 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146971) = 531441 * m + 74489 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 146971
  rw [data_20_146971.1, data_20_146971.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_146971 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 146971) < 1048576 * m + 146971 := by
  apply descent_of_endpoint
  · rw [data_20_146971.1]; exact data_20_146971.2.2
  · rw [data_20_146971.2.1]; decide

end Collatz.Research.FirstDescent.Batch268
