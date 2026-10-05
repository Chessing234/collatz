import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 300. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch300
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 239471). -/
theorem data_20_239471 : oddCount 239471 20 = 12 ∧
    acceleratedOrbit 20 239471 = 121370 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_239471 : ∀ j : Fin 20,
    239471 ≤ acceleratedOrbit j.val 239471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_239471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239471) = 531441 * m + 121370 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 239471
  rw [data_20_239471.1, data_20_239471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_239471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239471) < 1048576 * m + 239471 := by
  apply descent_of_endpoint
  · rw [data_20_239471.1]; exact data_20_239471.2.2
  · rw [data_20_239471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 240335). -/
theorem data_20_240335 : oddCount 240335 20 = 12 ∧
    acceleratedOrbit 20 240335 = 121808 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_240335 : ∀ j : Fin 20,
    240335 ≤ acceleratedOrbit j.val 240335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_240335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 240335) = 531441 * m + 121808 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 240335
  rw [data_20_240335.1, data_20_240335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_240335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 240335) < 1048576 * m + 240335 := by
  apply descent_of_endpoint
  · rw [data_20_240335.1]; exact data_20_240335.2.2
  · rw [data_20_240335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 240359). -/
theorem data_20_240359 : oddCount 240359 20 = 12 ∧
    acceleratedOrbit 20 240359 = 121820 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_240359 : ∀ j : Fin 20,
    240359 ≤ acceleratedOrbit j.val 240359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_240359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 240359) = 531441 * m + 121820 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 240359
  rw [data_20_240359.1, data_20_240359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_240359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 240359) < 1048576 * m + 240359 := by
  apply descent_of_endpoint
  · rw [data_20_240359.1]; exact data_20_240359.2.2
  · rw [data_20_240359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 240671). -/
theorem data_20_240671 : oddCount 240671 20 = 12 ∧
    acceleratedOrbit 20 240671 = 121978 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_240671 : ∀ j : Fin 20,
    240671 ≤ acceleratedOrbit j.val 240671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_240671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 240671) = 531441 * m + 121978 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 240671
  rw [data_20_240671.1, data_20_240671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_240671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 240671) < 1048576 * m + 240671 := by
  apply descent_of_endpoint
  · rw [data_20_240671.1]; exact data_20_240671.2.2
  · rw [data_20_240671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 241499). -/
theorem data_20_241499 : oddCount 241499 20 = 12 ∧
    acceleratedOrbit 20 241499 = 122398 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_241499 : ∀ j : Fin 20,
    241499 ≤ acceleratedOrbit j.val 241499 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_241499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 241499) = 531441 * m + 122398 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 241499
  rw [data_20_241499.1, data_20_241499.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_241499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 241499) < 1048576 * m + 241499 := by
  apply descent_of_endpoint
  · rw [data_20_241499.1]; exact data_20_241499.2.2
  · rw [data_20_241499.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 243431). -/
theorem data_20_243431 : oddCount 243431 20 = 12 ∧
    acceleratedOrbit 20 243431 = 123377 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_243431 : ∀ j : Fin 20,
    243431 ≤ acceleratedOrbit j.val 243431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_243431 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 243431) = 531441 * m + 123377 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 243431
  rw [data_20_243431.1, data_20_243431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_243431 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 243431) < 1048576 * m + 243431 := by
  apply descent_of_endpoint
  · rw [data_20_243431.1]; exact data_20_243431.2.2
  · rw [data_20_243431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 243567). -/
theorem data_20_243567 : oddCount 243567 20 = 12 ∧
    acceleratedOrbit 20 243567 = 123446 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_243567 : ∀ j : Fin 20,
    243567 ≤ acceleratedOrbit j.val 243567 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_243567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 243567) = 531441 * m + 123446 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 243567
  rw [data_20_243567.1, data_20_243567.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_243567 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 243567) < 1048576 * m + 243567 := by
  apply descent_of_endpoint
  · rw [data_20_243567.1]; exact data_20_243567.2.2
  · rw [data_20_243567.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 243583). -/
theorem data_20_243583 : oddCount 243583 20 = 12 ∧
    acceleratedOrbit 20 243583 = 123454 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_243583 : ∀ j : Fin 20,
    243583 ≤ acceleratedOrbit j.val 243583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_243583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 243583) = 531441 * m + 123454 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 243583
  rw [data_20_243583.1, data_20_243583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_243583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 243583) < 1048576 * m + 243583 := by
  apply descent_of_endpoint
  · rw [data_20_243583.1]; exact data_20_243583.2.2
  · rw [data_20_243583.2.1]; decide

end Collatz.Research.FirstDescent.Batch300
