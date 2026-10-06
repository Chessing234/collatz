import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 253. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch253
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 93467). -/
theorem data_20_93467 : oddCount 93467 20 = 12 ∧
    acceleratedOrbit 20 93467 = 47372 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_93467 : ∀ j : Fin 20,
    93467 ≤ acceleratedOrbit j.val 93467 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_93467 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 93467) = 531441 * m + 47372 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 93467
  rw [data_20_93467.1, data_20_93467.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_93467 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 93467) < 1048576 * m + 93467 := by
  apply descent_of_endpoint
  · rw [data_20_93467.1]; exact data_20_93467.2.2
  · rw [data_20_93467.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 93903). -/
theorem data_20_93903 : oddCount 93903 20 = 12 ∧
    acceleratedOrbit 20 93903 = 47593 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_93903 : ∀ j : Fin 20,
    93903 ≤ acceleratedOrbit j.val 93903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_93903 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 93903) = 531441 * m + 47593 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 93903
  rw [data_20_93903.1, data_20_93903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_93903 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 93903) < 1048576 * m + 93903 := by
  apply descent_of_endpoint
  · rw [data_20_93903.1]; exact data_20_93903.2.2
  · rw [data_20_93903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 93935). -/
theorem data_20_93935 : oddCount 93935 20 = 12 ∧
    acceleratedOrbit 20 93935 = 47609 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_93935 : ∀ j : Fin 20,
    93935 ≤ acceleratedOrbit j.val 93935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_93935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 93935) = 531441 * m + 47609 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 93935
  rw [data_20_93935.1, data_20_93935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_93935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 93935) < 1048576 * m + 93935 := by
  apply descent_of_endpoint
  · rw [data_20_93935.1]; exact data_20_93935.2.2
  · rw [data_20_93935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 94887). -/
theorem data_20_94887 : oddCount 94887 20 = 12 ∧
    acceleratedOrbit 20 94887 = 48092 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_94887 : ∀ j : Fin 20,
    94887 ≤ acceleratedOrbit j.val 94887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_94887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 94887) = 531441 * m + 48092 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 94887
  rw [data_20_94887.1, data_20_94887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_94887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 94887) < 1048576 * m + 94887 := by
  apply descent_of_endpoint
  · rw [data_20_94887.1]; exact data_20_94887.2.2
  · rw [data_20_94887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 95047). -/
theorem data_20_95047 : oddCount 95047 20 = 12 ∧
    acceleratedOrbit 20 95047 = 48173 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_95047 : ∀ j : Fin 20,
    95047 ≤ acceleratedOrbit j.val 95047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_95047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 95047) = 531441 * m + 48173 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 95047
  rw [data_20_95047.1, data_20_95047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_95047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 95047) < 1048576 * m + 95047 := by
  apply descent_of_endpoint
  · rw [data_20_95047.1]; exact data_20_95047.2.2
  · rw [data_20_95047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 95975). -/
theorem data_20_95975 : oddCount 95975 20 = 12 ∧
    acceleratedOrbit 20 95975 = 48643 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_95975 : ∀ j : Fin 20,
    95975 ≤ acceleratedOrbit j.val 95975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_95975 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 95975) = 531441 * m + 48643 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 95975
  rw [data_20_95975.1, data_20_95975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_95975 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 95975) < 1048576 * m + 95975 := by
  apply descent_of_endpoint
  · rw [data_20_95975.1]; exact data_20_95975.2.2
  · rw [data_20_95975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 96539). -/
theorem data_20_96539 : oddCount 96539 20 = 12 ∧
    acceleratedOrbit 20 96539 = 48929 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_96539 : ∀ j : Fin 20,
    96539 ≤ acceleratedOrbit j.val 96539 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_96539 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96539) = 531441 * m + 48929 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 96539
  rw [data_20_96539.1, data_20_96539.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_96539 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96539) < 1048576 * m + 96539 := by
  apply descent_of_endpoint
  · rw [data_20_96539.1]; exact data_20_96539.2.2
  · rw [data_20_96539.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 96575). -/
theorem data_20_96575 : oddCount 96575 20 = 12 ∧
    acceleratedOrbit 20 96575 = 48947 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_96575 : ∀ j : Fin 20,
    96575 ≤ acceleratedOrbit j.val 96575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_96575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96575) = 531441 * m + 48947 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 96575
  rw [data_20_96575.1, data_20_96575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_96575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 96575) < 1048576 * m + 96575 := by
  apply descent_of_endpoint
  · rw [data_20_96575.1]; exact data_20_96575.2.2
  · rw [data_20_96575.2.1]; decide

end Collatz.Research.FirstDescent.Batch253
