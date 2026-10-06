import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 234. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch234
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 37583). -/
theorem data_20_37583 : oddCount 37583 20 = 12 ∧
    acceleratedOrbit 20 37583 = 19049 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_37583 : ∀ j : Fin 20,
    37583 ≤ acceleratedOrbit j.val 37583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_37583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 37583) = 531441 * m + 19049 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 37583
  rw [data_20_37583.1, data_20_37583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_37583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 37583) < 1048576 * m + 37583 := by
  apply descent_of_endpoint
  · rw [data_20_37583.1]; exact data_20_37583.2.2
  · rw [data_20_37583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 38631). -/
theorem data_20_38631 : oddCount 38631 20 = 12 ∧
    acceleratedOrbit 20 38631 = 19580 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_38631 : ∀ j : Fin 20,
    38631 ≤ acceleratedOrbit j.val 38631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_38631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 38631) = 531441 * m + 19580 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 38631
  rw [data_20_38631.1, data_20_38631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_38631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 38631) < 1048576 * m + 38631 := by
  apply descent_of_endpoint
  · rw [data_20_38631.1]; exact data_20_38631.2.2
  · rw [data_20_38631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 39079). -/
theorem data_20_39079 : oddCount 39079 20 = 12 ∧
    acceleratedOrbit 20 39079 = 19807 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_39079 : ∀ j : Fin 20,
    39079 ≤ acceleratedOrbit j.val 39079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_39079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39079) = 531441 * m + 19807 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 39079
  rw [data_20_39079.1, data_20_39079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_39079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39079) < 1048576 * m + 39079 := by
  apply descent_of_endpoint
  · rw [data_20_39079.1]; exact data_20_39079.2.2
  · rw [data_20_39079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 39323). -/
theorem data_20_39323 : oddCount 39323 20 = 12 ∧
    acceleratedOrbit 20 39323 = 19931 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_39323 : ∀ j : Fin 20,
    39323 ≤ acceleratedOrbit j.val 39323 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_39323 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39323) = 531441 * m + 19931 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 39323
  rw [data_20_39323.1, data_20_39323.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_39323 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39323) < 1048576 * m + 39323 := by
  apply descent_of_endpoint
  · rw [data_20_39323.1]; exact data_20_39323.2.2
  · rw [data_20_39323.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 39423). -/
theorem data_20_39423 : oddCount 39423 20 = 12 ∧
    acceleratedOrbit 20 39423 = 19981 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_39423 : ∀ j : Fin 20,
    39423 ≤ acceleratedOrbit j.val 39423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_39423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39423) = 531441 * m + 19981 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 39423
  rw [data_20_39423.1, data_20_39423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_39423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39423) < 1048576 * m + 39423 := by
  apply descent_of_endpoint
  · rw [data_20_39423.1]; exact data_20_39423.2.2
  · rw [data_20_39423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 39963). -/
theorem data_20_39963 : oddCount 39963 20 = 12 ∧
    acceleratedOrbit 20 39963 = 20255 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_39963 : ∀ j : Fin 20,
    39963 ≤ acceleratedOrbit j.val 39963 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_39963 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39963) = 531441 * m + 20255 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 39963
  rw [data_20_39963.1, data_20_39963.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_39963 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 39963) < 1048576 * m + 39963 := by
  apply descent_of_endpoint
  · rw [data_20_39963.1]; exact data_20_39963.2.2
  · rw [data_20_39963.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 40091). -/
theorem data_20_40091 : oddCount 40091 20 = 12 ∧
    acceleratedOrbit 20 40091 = 20320 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_40091 : ∀ j : Fin 20,
    40091 ≤ acceleratedOrbit j.val 40091 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_40091 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40091) = 531441 * m + 20320 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 40091
  rw [data_20_40091.1, data_20_40091.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_40091 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40091) < 1048576 * m + 40091 := by
  apply descent_of_endpoint
  · rw [data_20_40091.1]; exact data_20_40091.2.2
  · rw [data_20_40091.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 40127). -/
theorem data_20_40127 : oddCount 40127 20 = 12 ∧
    acceleratedOrbit 20 40127 = 20338 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_40127 : ∀ j : Fin 20,
    40127 ≤ acceleratedOrbit j.val 40127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_40127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40127) = 531441 * m + 20338 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 40127
  rw [data_20_40127.1, data_20_40127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_40127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40127) < 1048576 * m + 40127 := by
  apply descent_of_endpoint
  · rw [data_20_40127.1]; exact data_20_40127.2.2
  · rw [data_20_40127.2.1]; decide

end Collatz.Research.FirstDescent.Batch234
