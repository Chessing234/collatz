import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 295. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch295
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 224507). -/
theorem data_20_224507 : oddCount 224507 20 = 12 ∧
    acceleratedOrbit 20 224507 = 113786 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_224507 : ∀ j : Fin 20,
    224507 ≤ acceleratedOrbit j.val 224507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_224507 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224507) = 531441 * m + 113786 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 224507
  rw [data_20_224507.1, data_20_224507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_224507 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224507) < 1048576 * m + 224507 := by
  apply descent_of_endpoint
  · rw [data_20_224507.1]; exact data_20_224507.2.2
  · rw [data_20_224507.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 224671). -/
theorem data_20_224671 : oddCount 224671 20 = 12 ∧
    acceleratedOrbit 20 224671 = 113869 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_224671 : ∀ j : Fin 20,
    224671 ≤ acceleratedOrbit j.val 224671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_224671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224671) = 531441 * m + 113869 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 224671
  rw [data_20_224671.1, data_20_224671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_224671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224671) < 1048576 * m + 224671 := by
  apply descent_of_endpoint
  · rw [data_20_224671.1]; exact data_20_224671.2.2
  · rw [data_20_224671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 224795). -/
theorem data_20_224795 : oddCount 224795 20 = 12 ∧
    acceleratedOrbit 20 224795 = 113932 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_224795 : ∀ j : Fin 20,
    224795 ≤ acceleratedOrbit j.val 224795 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_224795 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224795) = 531441 * m + 113932 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 224795
  rw [data_20_224795.1, data_20_224795.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_224795 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224795) < 1048576 * m + 224795 := by
  apply descent_of_endpoint
  · rw [data_20_224795.1]; exact data_20_224795.2.2
  · rw [data_20_224795.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 224815). -/
theorem data_20_224815 : oddCount 224815 20 = 12 ∧
    acceleratedOrbit 20 224815 = 113942 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_224815 : ∀ j : Fin 20,
    224815 ≤ acceleratedOrbit j.val 224815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_224815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224815) = 531441 * m + 113942 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 224815
  rw [data_20_224815.1, data_20_224815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_224815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 224815) < 1048576 * m + 224815 := by
  apply descent_of_endpoint
  · rw [data_20_224815.1]; exact data_20_224815.2.2
  · rw [data_20_224815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 225371). -/
theorem data_20_225371 : oddCount 225371 20 = 12 ∧
    acceleratedOrbit 20 225371 = 114224 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_225371 : ∀ j : Fin 20,
    225371 ≤ acceleratedOrbit j.val 225371 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_225371 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 225371) = 531441 * m + 114224 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 225371
  rw [data_20_225371.1, data_20_225371.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_225371 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 225371) < 1048576 * m + 225371 := by
  apply descent_of_endpoint
  · rw [data_20_225371.1]; exact data_20_225371.2.2
  · rw [data_20_225371.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 225727). -/
theorem data_20_225727 : oddCount 225727 20 = 12 ∧
    acceleratedOrbit 20 225727 = 114404 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_225727 : ∀ j : Fin 20,
    225727 ≤ acceleratedOrbit j.val 225727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_225727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 225727) = 531441 * m + 114404 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 225727
  rw [data_20_225727.1, data_20_225727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_225727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 225727) < 1048576 * m + 225727 := by
  apply descent_of_endpoint
  · rw [data_20_225727.1]; exact data_20_225727.2.2
  · rw [data_20_225727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 226175). -/
theorem data_20_226175 : oddCount 226175 20 = 12 ∧
    acceleratedOrbit 20 226175 = 114631 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_226175 : ∀ j : Fin 20,
    226175 ≤ acceleratedOrbit j.val 226175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_226175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 226175) = 531441 * m + 114631 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 226175
  rw [data_20_226175.1, data_20_226175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_226175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 226175) < 1048576 * m + 226175 := by
  apply descent_of_endpoint
  · rw [data_20_226175.1]; exact data_20_226175.2.2
  · rw [data_20_226175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 226271). -/
theorem data_20_226271 : oddCount 226271 20 = 12 ∧
    acceleratedOrbit 20 226271 = 114680 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_226271 : ∀ j : Fin 20,
    226271 ≤ acceleratedOrbit j.val 226271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_226271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 226271) = 531441 * m + 114680 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 226271
  rw [data_20_226271.1, data_20_226271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_226271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 226271) < 1048576 * m + 226271 := by
  apply descent_of_endpoint
  · rw [data_20_226271.1]; exact data_20_226271.2.2
  · rw [data_20_226271.2.1]; decide

end Collatz.Research.FirstDescent.Batch295
