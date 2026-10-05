import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 262. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch262
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 124991). -/
theorem data_20_124991 : oddCount 124991 20 = 12 ∧
    acceleratedOrbit 20 124991 = 63349 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_124991 : ∀ j : Fin 20,
    124991 ≤ acceleratedOrbit j.val 124991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_124991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 124991) = 531441 * m + 63349 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 124991
  rw [data_20_124991.1, data_20_124991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_124991 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 124991) < 1048576 * m + 124991 := by
  apply descent_of_endpoint
  · rw [data_20_124991.1]; exact data_20_124991.2.2
  · rw [data_20_124991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 125423). -/
theorem data_20_125423 : oddCount 125423 20 = 12 ∧
    acceleratedOrbit 20 125423 = 63568 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_125423 : ∀ j : Fin 20,
    125423 ≤ acceleratedOrbit j.val 125423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_125423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 125423) = 531441 * m + 63568 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 125423
  rw [data_20_125423.1, data_20_125423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_125423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 125423) < 1048576 * m + 125423 := by
  apply descent_of_endpoint
  · rw [data_20_125423.1]; exact data_20_125423.2.2
  · rw [data_20_125423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 125531). -/
theorem data_20_125531 : oddCount 125531 20 = 12 ∧
    acceleratedOrbit 20 125531 = 63623 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_125531 : ∀ j : Fin 20,
    125531 ≤ acceleratedOrbit j.val 125531 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_125531 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 125531) = 531441 * m + 63623 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 125531
  rw [data_20_125531.1, data_20_125531.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_125531 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 125531) < 1048576 * m + 125531 := by
  apply descent_of_endpoint
  · rw [data_20_125531.1]; exact data_20_125531.2.2
  · rw [data_20_125531.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 125887). -/
theorem data_20_125887 : oddCount 125887 20 = 12 ∧
    acceleratedOrbit 20 125887 = 63803 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_125887 : ∀ j : Fin 20,
    125887 ≤ acceleratedOrbit j.val 125887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_125887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 125887) = 531441 * m + 63803 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 125887
  rw [data_20_125887.1, data_20_125887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_125887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 125887) < 1048576 * m + 125887 := by
  apply descent_of_endpoint
  · rw [data_20_125887.1]; exact data_20_125887.2.2
  · rw [data_20_125887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 127023). -/
theorem data_20_127023 : oddCount 127023 20 = 12 ∧
    acceleratedOrbit 20 127023 = 64379 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_127023 : ∀ j : Fin 20,
    127023 ≤ acceleratedOrbit j.val 127023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_127023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 127023) = 531441 * m + 64379 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 127023
  rw [data_20_127023.1, data_20_127023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_127023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 127023) < 1048576 * m + 127023 := by
  apply descent_of_endpoint
  · rw [data_20_127023.1]; exact data_20_127023.2.2
  · rw [data_20_127023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 127935). -/
theorem data_20_127935 : oddCount 127935 20 = 12 ∧
    acceleratedOrbit 20 127935 = 64841 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_127935 : ∀ j : Fin 20,
    127935 ≤ acceleratedOrbit j.val 127935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_127935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 127935) = 531441 * m + 64841 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 127935
  rw [data_20_127935.1, data_20_127935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_127935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 127935) < 1048576 * m + 127935 := by
  apply descent_of_endpoint
  · rw [data_20_127935.1]; exact data_20_127935.2.2
  · rw [data_20_127935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 128935). -/
theorem data_20_128935 : oddCount 128935 20 = 12 ∧
    acceleratedOrbit 20 128935 = 65348 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_128935 : ∀ j : Fin 20,
    128935 ≤ acceleratedOrbit j.val 128935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_128935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 128935) = 531441 * m + 65348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 128935
  rw [data_20_128935.1, data_20_128935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_128935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 128935) < 1048576 * m + 128935 := by
  apply descent_of_endpoint
  · rw [data_20_128935.1]; exact data_20_128935.2.2
  · rw [data_20_128935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 129231). -/
theorem data_20_129231 : oddCount 129231 20 = 12 ∧
    acceleratedOrbit 20 129231 = 65498 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_129231 : ∀ j : Fin 20,
    129231 ≤ acceleratedOrbit j.val 129231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_129231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 129231) = 531441 * m + 65498 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 129231
  rw [data_20_129231.1, data_20_129231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_129231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 129231) < 1048576 * m + 129231 := by
  apply descent_of_endpoint
  · rw [data_20_129231.1]; exact data_20_129231.2.2
  · rw [data_20_129231.2.1]; decide

end Collatz.Research.FirstDescent.Batch262
