import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 245. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch245
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 70655). -/
theorem data_20_70655 : oddCount 70655 20 = 12 ∧
    acceleratedOrbit 20 70655 = 35810 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_70655 : ∀ j : Fin 20,
    70655 ≤ acceleratedOrbit j.val 70655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_70655 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 70655) = 531441 * m + 35810 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 70655
  rw [data_20_70655.1, data_20_70655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_70655 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 70655) < 1048576 * m + 70655 := by
  apply descent_of_endpoint
  · rw [data_20_70655.1]; exact data_20_70655.2.2
  · rw [data_20_70655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 70759). -/
theorem data_20_70759 : oddCount 70759 20 = 12 ∧
    acceleratedOrbit 20 70759 = 35863 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_70759 : ∀ j : Fin 20,
    70759 ≤ acceleratedOrbit j.val 70759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_70759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 70759) = 531441 * m + 35863 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 70759
  rw [data_20_70759.1, data_20_70759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_70759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 70759) < 1048576 * m + 70759 := by
  apply descent_of_endpoint
  · rw [data_20_70759.1]; exact data_20_70759.2.2
  · rw [data_20_70759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 70783). -/
theorem data_20_70783 : oddCount 70783 20 = 12 ∧
    acceleratedOrbit 20 70783 = 35875 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_70783 : ∀ j : Fin 20,
    70783 ≤ acceleratedOrbit j.val 70783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_70783 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 70783) = 531441 * m + 35875 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 70783
  rw [data_20_70783.1, data_20_70783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_70783 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 70783) < 1048576 * m + 70783 := by
  apply descent_of_endpoint
  · rw [data_20_70783.1]; exact data_20_70783.2.2
  · rw [data_20_70783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 71039). -/
theorem data_20_71039 : oddCount 71039 20 = 12 ∧
    acceleratedOrbit 20 71039 = 36005 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_71039 : ∀ j : Fin 20,
    71039 ≤ acceleratedOrbit j.val 71039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_71039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 71039) = 531441 * m + 36005 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 71039
  rw [data_20_71039.1, data_20_71039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_71039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 71039) < 1048576 * m + 71039 := by
  apply descent_of_endpoint
  · rw [data_20_71039.1]; exact data_20_71039.2.2
  · rw [data_20_71039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 71679). -/
theorem data_20_71679 : oddCount 71679 20 = 12 ∧
    acceleratedOrbit 20 71679 = 36329 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_71679 : ∀ j : Fin 20,
    71679 ≤ acceleratedOrbit j.val 71679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_71679 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 71679) = 531441 * m + 36329 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 71679
  rw [data_20_71679.1, data_20_71679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_71679 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 71679) < 1048576 * m + 71679 := by
  apply descent_of_endpoint
  · rw [data_20_71679.1]; exact data_20_71679.2.2
  · rw [data_20_71679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 71771). -/
theorem data_20_71771 : oddCount 71771 20 = 12 ∧
    acceleratedOrbit 20 71771 = 36376 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_71771 : ∀ j : Fin 20,
    71771 ≤ acceleratedOrbit j.val 71771 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_71771 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 71771) = 531441 * m + 36376 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 71771
  rw [data_20_71771.1, data_20_71771.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_71771 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 71771) < 1048576 * m + 71771 := by
  apply descent_of_endpoint
  · rw [data_20_71771.1]; exact data_20_71771.2.2
  · rw [data_20_71771.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 72347). -/
theorem data_20_72347 : oddCount 72347 20 = 12 ∧
    acceleratedOrbit 20 72347 = 36668 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_72347 : ∀ j : Fin 20,
    72347 ≤ acceleratedOrbit j.val 72347 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_72347 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72347) = 531441 * m + 36668 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 72347
  rw [data_20_72347.1, data_20_72347.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_72347 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72347) < 1048576 * m + 72347 := by
  apply descent_of_endpoint
  · rw [data_20_72347.1]; exact data_20_72347.2.2
  · rw [data_20_72347.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 72359). -/
theorem data_20_72359 : oddCount 72359 20 = 12 ∧
    acceleratedOrbit 20 72359 = 36674 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_72359 : ∀ j : Fin 20,
    72359 ≤ acceleratedOrbit j.val 72359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_72359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72359) = 531441 * m + 36674 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 72359
  rw [data_20_72359.1, data_20_72359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_72359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 72359) < 1048576 * m + 72359 := by
  apply descent_of_endpoint
  · rw [data_20_72359.1]; exact data_20_72359.2.2
  · rw [data_20_72359.2.1]; decide

end Collatz.Research.FirstDescent.Batch245
