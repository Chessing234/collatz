import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 258. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch258
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 109183). -/
theorem data_20_109183 : oddCount 109183 20 = 12 ∧
    acceleratedOrbit 20 109183 = 55337 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_109183 : ∀ j : Fin 20,
    109183 ≤ acceleratedOrbit j.val 109183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_109183 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 109183) = 531441 * m + 55337 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 109183
  rw [data_20_109183.1, data_20_109183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_109183 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 109183) < 1048576 * m + 109183 := by
  apply descent_of_endpoint
  · rw [data_20_109183.1]; exact data_20_109183.2.2
  · rw [data_20_109183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 109595). -/
theorem data_20_109595 : oddCount 109595 20 = 12 ∧
    acceleratedOrbit 20 109595 = 55546 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_109595 : ∀ j : Fin 20,
    109595 ≤ acceleratedOrbit j.val 109595 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_109595 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 109595) = 531441 * m + 55546 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 109595
  rw [data_20_109595.1, data_20_109595.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_109595 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 109595) < 1048576 * m + 109595 := by
  apply descent_of_endpoint
  · rw [data_20_109595.1]; exact data_20_109595.2.2
  · rw [data_20_109595.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 110311). -/
theorem data_20_110311 : oddCount 110311 20 = 12 ∧
    acceleratedOrbit 20 110311 = 55909 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_110311 : ∀ j : Fin 20,
    110311 ≤ acceleratedOrbit j.val 110311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_110311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 110311) = 531441 * m + 55909 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 110311
  rw [data_20_110311.1, data_20_110311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_110311 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 110311) < 1048576 * m + 110311 := by
  apply descent_of_endpoint
  · rw [data_20_110311.1]; exact data_20_110311.2.2
  · rw [data_20_110311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 111087). -/
theorem data_20_111087 : oddCount 111087 20 = 12 ∧
    acceleratedOrbit 20 111087 = 56302 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_111087 : ∀ j : Fin 20,
    111087 ≤ acceleratedOrbit j.val 111087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_111087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 111087) = 531441 * m + 56302 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 111087
  rw [data_20_111087.1, data_20_111087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_111087 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 111087) < 1048576 * m + 111087 := by
  apply descent_of_endpoint
  · rw [data_20_111087.1]; exact data_20_111087.2.2
  · rw [data_20_111087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 111195). -/
theorem data_20_111195 : oddCount 111195 20 = 12 ∧
    acceleratedOrbit 20 111195 = 56357 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_111195 : ∀ j : Fin 20,
    111195 ≤ acceleratedOrbit j.val 111195 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_111195 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 111195) = 531441 * m + 56357 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 111195
  rw [data_20_111195.1, data_20_111195.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_111195 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 111195) < 1048576 * m + 111195 := by
  apply descent_of_endpoint
  · rw [data_20_111195.1]; exact data_20_111195.2.2
  · rw [data_20_111195.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 111643). -/
theorem data_20_111643 : oddCount 111643 20 = 12 ∧
    acceleratedOrbit 20 111643 = 56584 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_111643 : ∀ j : Fin 20,
    111643 ≤ acceleratedOrbit j.val 111643 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_111643 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 111643) = 531441 * m + 56584 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 111643
  rw [data_20_111643.1, data_20_111643.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_111643 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 111643) < 1048576 * m + 111643 := by
  apply descent_of_endpoint
  · rw [data_20_111643.1]; exact data_20_111643.2.2
  · rw [data_20_111643.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 112095). -/
theorem data_20_112095 : oddCount 112095 20 = 12 ∧
    acceleratedOrbit 20 112095 = 56813 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_112095 : ∀ j : Fin 20,
    112095 ≤ acceleratedOrbit j.val 112095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_112095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 112095) = 531441 * m + 56813 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 112095
  rw [data_20_112095.1, data_20_112095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_112095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 112095) < 1048576 * m + 112095 := by
  apply descent_of_endpoint
  · rw [data_20_112095.1]; exact data_20_112095.2.2
  · rw [data_20_112095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 112255). -/
theorem data_20_112255 : oddCount 112255 20 = 12 ∧
    acceleratedOrbit 20 112255 = 56894 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_112255 : ∀ j : Fin 20,
    112255 ≤ acceleratedOrbit j.val 112255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_112255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 112255) = 531441 * m + 56894 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 112255
  rw [data_20_112255.1, data_20_112255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_112255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 112255) < 1048576 * m + 112255 := by
  apply descent_of_endpoint
  · rw [data_20_112255.1]; exact data_20_112255.2.2
  · rw [data_20_112255.2.1]; decide

end Collatz.Research.FirstDescent.Batch258
