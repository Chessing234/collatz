import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 240. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch240
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 53735). -/
theorem data_20_53735 : oddCount 53735 20 = 12 ∧
    acceleratedOrbit 20 53735 = 27235 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_53735 : ∀ j : Fin 20,
    53735 ≤ acceleratedOrbit j.val 53735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_53735 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 53735) = 531441 * m + 27235 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 53735
  rw [data_20_53735.1, data_20_53735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_53735 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 53735) < 1048576 * m + 53735 := by
  apply descent_of_endpoint
  · rw [data_20_53735.1]; exact data_20_53735.2.2
  · rw [data_20_53735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 54463). -/
theorem data_20_54463 : oddCount 54463 20 = 12 ∧
    acceleratedOrbit 20 54463 = 27604 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_54463 : ∀ j : Fin 20,
    54463 ≤ acceleratedOrbit j.val 54463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_54463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 54463) = 531441 * m + 27604 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 54463
  rw [data_20_54463.1, data_20_54463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_54463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 54463) < 1048576 * m + 54463 := by
  apply descent_of_endpoint
  · rw [data_20_54463.1]; exact data_20_54463.2.2
  · rw [data_20_54463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 54631). -/
theorem data_20_54631 : oddCount 54631 20 = 12 ∧
    acceleratedOrbit 20 54631 = 27689 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_54631 : ∀ j : Fin 20,
    54631 ≤ acceleratedOrbit j.val 54631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_54631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 54631) = 531441 * m + 27689 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 54631
  rw [data_20_54631.1, data_20_54631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_54631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 54631) < 1048576 * m + 54631 := by
  apply descent_of_endpoint
  · rw [data_20_54631.1]; exact data_20_54631.2.2
  · rw [data_20_54631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 54783). -/
theorem data_20_54783 : oddCount 54783 20 = 12 ∧
    acceleratedOrbit 20 54783 = 27766 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_54783 : ∀ j : Fin 20,
    54783 ≤ acceleratedOrbit j.val 54783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_54783 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 54783) = 531441 * m + 27766 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 54783
  rw [data_20_54783.1, data_20_54783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_54783 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 54783) < 1048576 * m + 54783 := by
  apply descent_of_endpoint
  · rw [data_20_54783.1]; exact data_20_54783.2.2
  · rw [data_20_54783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 55323). -/
theorem data_20_55323 : oddCount 55323 20 = 12 ∧
    acceleratedOrbit 20 55323 = 28040 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_55323 : ∀ j : Fin 20,
    55323 ≤ acceleratedOrbit j.val 55323 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_55323 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 55323) = 531441 * m + 28040 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 55323
  rw [data_20_55323.1, data_20_55323.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_55323 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 55323) < 1048576 * m + 55323 := by
  apply descent_of_endpoint
  · rw [data_20_55323.1]; exact data_20_55323.2.2
  · rw [data_20_55323.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 55359). -/
theorem data_20_55359 : oddCount 55359 20 = 12 ∧
    acceleratedOrbit 20 55359 = 28058 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_55359 : ∀ j : Fin 20,
    55359 ≤ acceleratedOrbit j.val 55359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_55359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 55359) = 531441 * m + 28058 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 55359
  rw [data_20_55359.1, data_20_55359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_55359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 55359) < 1048576 * m + 55359 := by
  apply descent_of_endpoint
  · rw [data_20_55359.1]; exact data_20_55359.2.2
  · rw [data_20_55359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 56559). -/
theorem data_20_56559 : oddCount 56559 20 = 12 ∧
    acceleratedOrbit 20 56559 = 28666 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_56559 : ∀ j : Fin 20,
    56559 ≤ acceleratedOrbit j.val 56559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_56559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 56559) = 531441 * m + 28666 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 56559
  rw [data_20_56559.1, data_20_56559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_56559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 56559) < 1048576 * m + 56559 := by
  apply descent_of_endpoint
  · rw [data_20_56559.1]; exact data_20_56559.2.2
  · rw [data_20_56559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 56815). -/
theorem data_20_56815 : oddCount 56815 20 = 12 ∧
    acceleratedOrbit 20 56815 = 28796 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_56815 : ∀ j : Fin 20,
    56815 ≤ acceleratedOrbit j.val 56815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_56815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 56815) = 531441 * m + 28796 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 56815
  rw [data_20_56815.1, data_20_56815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_56815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 56815) < 1048576 * m + 56815 := by
  apply descent_of_endpoint
  · rw [data_20_56815.1]; exact data_20_56815.2.2
  · rw [data_20_56815.2.1]; decide

end Collatz.Research.FirstDescent.Batch240
