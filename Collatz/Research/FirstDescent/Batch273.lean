import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 273. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch273
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 160423). -/
theorem data_20_160423 : oddCount 160423 20 = 12 ∧
    acceleratedOrbit 20 160423 = 81307 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_160423 : ∀ j : Fin 20,
    160423 ≤ acceleratedOrbit j.val 160423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_160423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 160423) = 531441 * m + 81307 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 160423
  rw [data_20_160423.1, data_20_160423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_160423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 160423) < 1048576 * m + 160423 := by
  apply descent_of_endpoint
  · rw [data_20_160423.1]; exact data_20_160423.2.2
  · rw [data_20_160423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 160583). -/
theorem data_20_160583 : oddCount 160583 20 = 12 ∧
    acceleratedOrbit 20 160583 = 81388 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_160583 : ∀ j : Fin 20,
    160583 ≤ acceleratedOrbit j.val 160583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_160583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 160583) = 531441 * m + 81388 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 160583
  rw [data_20_160583.1, data_20_160583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_160583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 160583) < 1048576 * m + 160583 := by
  apply descent_of_endpoint
  · rw [data_20_160583.1]; exact data_20_160583.2.2
  · rw [data_20_160583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 161639). -/
theorem data_20_161639 : oddCount 161639 20 = 12 ∧
    acceleratedOrbit 20 161639 = 81923 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_161639 : ∀ j : Fin 20,
    161639 ≤ acceleratedOrbit j.val 161639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_161639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 161639) = 531441 * m + 81923 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 161639
  rw [data_20_161639.1, data_20_161639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_161639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 161639) < 1048576 * m + 161639 := by
  apply descent_of_endpoint
  · rw [data_20_161639.1]; exact data_20_161639.2.2
  · rw [data_20_161639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 162663). -/
theorem data_20_162663 : oddCount 162663 20 = 12 ∧
    acceleratedOrbit 20 162663 = 82442 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_162663 : ∀ j : Fin 20,
    162663 ≤ acceleratedOrbit j.val 162663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_162663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 162663) = 531441 * m + 82442 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 162663
  rw [data_20_162663.1, data_20_162663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_162663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 162663) < 1048576 * m + 162663 := by
  apply descent_of_endpoint
  · rw [data_20_162663.1]; exact data_20_162663.2.2
  · rw [data_20_162663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 162687). -/
theorem data_20_162687 : oddCount 162687 20 = 12 ∧
    acceleratedOrbit 20 162687 = 82454 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_162687 : ∀ j : Fin 20,
    162687 ≤ acceleratedOrbit j.val 162687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_162687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 162687) = 531441 * m + 82454 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 162687
  rw [data_20_162687.1, data_20_162687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_162687 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 162687) < 1048576 * m + 162687 := by
  apply descent_of_endpoint
  · rw [data_20_162687.1]; exact data_20_162687.2.2
  · rw [data_20_162687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 163099). -/
theorem data_20_163099 : oddCount 163099 20 = 12 ∧
    acceleratedOrbit 20 163099 = 82663 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_163099 : ∀ j : Fin 20,
    163099 ≤ acceleratedOrbit j.val 163099 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_163099 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 163099) = 531441 * m + 82663 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 163099
  rw [data_20_163099.1, data_20_163099.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_163099 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 163099) < 1048576 * m + 163099 := by
  apply descent_of_endpoint
  · rw [data_20_163099.1]; exact data_20_163099.2.2
  · rw [data_20_163099.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 163823). -/
theorem data_20_163823 : oddCount 163823 20 = 12 ∧
    acceleratedOrbit 20 163823 = 83030 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_163823 : ∀ j : Fin 20,
    163823 ≤ acceleratedOrbit j.val 163823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_163823 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 163823) = 531441 * m + 83030 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 163823
  rw [data_20_163823.1, data_20_163823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_163823 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 163823) < 1048576 * m + 163823 := by
  apply descent_of_endpoint
  · rw [data_20_163823.1]; exact data_20_163823.2.2
  · rw [data_20_163823.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 164591). -/
theorem data_20_164591 : oddCount 164591 20 = 12 ∧
    acceleratedOrbit 20 164591 = 83419 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_164591 : ∀ j : Fin 20,
    164591 ≤ acceleratedOrbit j.val 164591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_164591 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 164591) = 531441 * m + 83419 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 164591
  rw [data_20_164591.1, data_20_164591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_164591 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 164591) < 1048576 * m + 164591 := by
  apply descent_of_endpoint
  · rw [data_20_164591.1]; exact data_20_164591.2.2
  · rw [data_20_164591.2.1]; decide

end Collatz.Research.FirstDescent.Batch273
