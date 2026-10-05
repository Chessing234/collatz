import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 293. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch293
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 219239). -/
theorem data_20_219239 : oddCount 219239 20 = 12 ∧
    acceleratedOrbit 20 219239 = 111116 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_219239 : ∀ j : Fin 20,
    219239 ≤ acceleratedOrbit j.val 219239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_219239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 219239) = 531441 * m + 111116 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 219239
  rw [data_20_219239.1, data_20_219239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_219239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 219239) < 1048576 * m + 219239 := by
  apply descent_of_endpoint
  · rw [data_20_219239.1]; exact data_20_219239.2.2
  · rw [data_20_219239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 219583). -/
theorem data_20_219583 : oddCount 219583 20 = 12 ∧
    acceleratedOrbit 20 219583 = 111290 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_219583 : ∀ j : Fin 20,
    219583 ≤ acceleratedOrbit j.val 219583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_219583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 219583) = 531441 * m + 111290 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 219583
  rw [data_20_219583.1, data_20_219583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_219583 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 219583) < 1048576 * m + 219583 := by
  apply descent_of_endpoint
  · rw [data_20_219583.1]; exact data_20_219583.2.2
  · rw [data_20_219583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 220719). -/
theorem data_20_220719 : oddCount 220719 20 = 12 ∧
    acceleratedOrbit 20 220719 = 111866 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_220719 : ∀ j : Fin 20,
    220719 ≤ acceleratedOrbit j.val 220719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_220719 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 220719) = 531441 * m + 111866 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 220719
  rw [data_20_220719.1, data_20_220719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_220719 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 220719) < 1048576 * m + 220719 := by
  apply descent_of_endpoint
  · rw [data_20_220719.1]; exact data_20_220719.2.2
  · rw [data_20_220719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 221031). -/
theorem data_20_221031 : oddCount 221031 20 = 12 ∧
    acceleratedOrbit 20 221031 = 112024 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_221031 : ∀ j : Fin 20,
    221031 ≤ acceleratedOrbit j.val 221031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_221031 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221031) = 531441 * m + 112024 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 221031
  rw [data_20_221031.1, data_20_221031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_221031 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221031) < 1048576 * m + 221031 := by
  apply descent_of_endpoint
  · rw [data_20_221031.1]; exact data_20_221031.2.2
  · rw [data_20_221031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 221435). -/
theorem data_20_221435 : oddCount 221435 20 = 12 ∧
    acceleratedOrbit 20 221435 = 112229 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_221435 : ∀ j : Fin 20,
    221435 ≤ acceleratedOrbit j.val 221435 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_221435 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221435) = 531441 * m + 112229 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 221435
  rw [data_20_221435.1, data_20_221435.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_221435 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221435) < 1048576 * m + 221435 := by
  apply descent_of_endpoint
  · rw [data_20_221435.1]; exact data_20_221435.2.2
  · rw [data_20_221435.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 221599). -/
theorem data_20_221599 : oddCount 221599 20 = 12 ∧
    acceleratedOrbit 20 221599 = 112312 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_221599 : ∀ j : Fin 20,
    221599 ≤ acceleratedOrbit j.val 221599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_221599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221599) = 531441 * m + 112312 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 221599
  rw [data_20_221599.1, data_20_221599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_221599 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221599) < 1048576 * m + 221599 := by
  apply descent_of_endpoint
  · rw [data_20_221599.1]; exact data_20_221599.2.2
  · rw [data_20_221599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 221631). -/
theorem data_20_221631 : oddCount 221631 20 = 12 ∧
    acceleratedOrbit 20 221631 = 112328 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_221631 : ∀ j : Fin 20,
    221631 ≤ acceleratedOrbit j.val 221631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_221631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221631) = 531441 * m + 112328 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 221631
  rw [data_20_221631.1, data_20_221631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_221631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 221631) < 1048576 * m + 221631 := by
  apply descent_of_endpoint
  · rw [data_20_221631.1]; exact data_20_221631.2.2
  · rw [data_20_221631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 222015). -/
theorem data_20_222015 : oddCount 222015 20 = 12 ∧
    acceleratedOrbit 20 222015 = 112523 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_222015 : ∀ j : Fin 20,
    222015 ≤ acceleratedOrbit j.val 222015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_222015 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222015) = 531441 * m + 112523 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 222015
  rw [data_20_222015.1, data_20_222015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_222015 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 222015) < 1048576 * m + 222015 := by
  apply descent_of_endpoint
  · rw [data_20_222015.1]; exact data_20_222015.2.2
  · rw [data_20_222015.2.1]; decide

end Collatz.Research.FirstDescent.Batch293
