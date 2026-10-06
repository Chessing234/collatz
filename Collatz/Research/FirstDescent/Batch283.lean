import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 283. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch283
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 191259). -/
theorem data_20_191259 : oddCount 191259 20 = 12 ∧
    acceleratedOrbit 20 191259 = 96935 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_191259 : ∀ j : Fin 20,
    191259 ≤ acceleratedOrbit j.val 191259 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_191259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191259) = 531441 * m + 96935 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 191259
  rw [data_20_191259.1, data_20_191259.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_191259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191259) < 1048576 * m + 191259 := by
  apply descent_of_endpoint
  · rw [data_20_191259.1]; exact data_20_191259.2.2
  · rw [data_20_191259.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 191423). -/
theorem data_20_191423 : oddCount 191423 20 = 12 ∧
    acceleratedOrbit 20 191423 = 97018 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_191423 : ∀ j : Fin 20,
    191423 ≤ acceleratedOrbit j.val 191423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_191423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191423) = 531441 * m + 97018 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 191423
  rw [data_20_191423.1, data_20_191423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_191423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191423) < 1048576 * m + 191423 := by
  apply descent_of_endpoint
  · rw [data_20_191423.1]; exact data_20_191423.2.2
  · rw [data_20_191423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 191727). -/
theorem data_20_191727 : oddCount 191727 20 = 12 ∧
    acceleratedOrbit 20 191727 = 97172 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_191727 : ∀ j : Fin 20,
    191727 ≤ acceleratedOrbit j.val 191727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_191727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191727) = 531441 * m + 97172 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 191727
  rw [data_20_191727.1, data_20_191727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_191727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191727) < 1048576 * m + 191727 := by
  apply descent_of_endpoint
  · rw [data_20_191727.1]; exact data_20_191727.2.2
  · rw [data_20_191727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 191791). -/
theorem data_20_191791 : oddCount 191791 20 = 12 ∧
    acceleratedOrbit 20 191791 = 97205 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_191791 : ∀ j : Fin 20,
    191791 ≤ acceleratedOrbit j.val 191791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_191791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191791) = 531441 * m + 97205 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 191791
  rw [data_20_191791.1, data_20_191791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_191791 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191791) < 1048576 * m + 191791 := by
  apply descent_of_endpoint
  · rw [data_20_191791.1]; exact data_20_191791.2.2
  · rw [data_20_191791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 191951). -/
theorem data_20_191951 : oddCount 191951 20 = 12 ∧
    acceleratedOrbit 20 191951 = 97286 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_191951 : ∀ j : Fin 20,
    191951 ≤ acceleratedOrbit j.val 191951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_191951 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191951) = 531441 * m + 97286 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 191951
  rw [data_20_191951.1, data_20_191951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_191951 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 191951) < 1048576 * m + 191951 := by
  apply descent_of_endpoint
  · rw [data_20_191951.1]; exact data_20_191951.2.2
  · rw [data_20_191951.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 192111). -/
theorem data_20_192111 : oddCount 192111 20 = 12 ∧
    acceleratedOrbit 20 192111 = 97367 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_192111 : ∀ j : Fin 20,
    192111 ≤ acceleratedOrbit j.val 192111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_192111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192111) = 531441 * m + 97367 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 192111
  rw [data_20_192111.1, data_20_192111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_192111 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192111) < 1048576 * m + 192111 := by
  apply descent_of_endpoint
  · rw [data_20_192111.1]; exact data_20_192111.2.2
  · rw [data_20_192111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 192559). -/
theorem data_20_192559 : oddCount 192559 20 = 12 ∧
    acceleratedOrbit 20 192559 = 97594 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_192559 : ∀ j : Fin 20,
    192559 ≤ acceleratedOrbit j.val 192559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_192559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192559) = 531441 * m + 97594 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 192559
  rw [data_20_192559.1, data_20_192559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_192559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192559) < 1048576 * m + 192559 := by
  apply descent_of_endpoint
  · rw [data_20_192559.1]; exact data_20_192559.2.2
  · rw [data_20_192559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 192815). -/
theorem data_20_192815 : oddCount 192815 20 = 12 ∧
    acceleratedOrbit 20 192815 = 97724 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_192815 : ∀ j : Fin 20,
    192815 ≤ acceleratedOrbit j.val 192815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_192815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192815) = 531441 * m + 97724 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 192815
  rw [data_20_192815.1, data_20_192815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_192815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192815) < 1048576 * m + 192815 := by
  apply descent_of_endpoint
  · rw [data_20_192815.1]; exact data_20_192815.2.2
  · rw [data_20_192815.2.1]; decide

end Collatz.Research.FirstDescent.Batch283
