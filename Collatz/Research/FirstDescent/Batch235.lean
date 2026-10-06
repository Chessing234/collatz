import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 235. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch235
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 40239). -/
theorem data_20_40239 : oddCount 40239 20 = 12 ∧
    acceleratedOrbit 20 40239 = 20395 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_40239 : ∀ j : Fin 20,
    40239 ≤ acceleratedOrbit j.val 40239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_40239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40239) = 531441 * m + 20395 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 40239
  rw [data_20_40239.1, data_20_40239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_40239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40239) < 1048576 * m + 40239 := by
  apply descent_of_endpoint
  · rw [data_20_40239.1]; exact data_20_40239.2.2
  · rw [data_20_40239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 40347). -/
theorem data_20_40347 : oddCount 40347 20 = 12 ∧
    acceleratedOrbit 20 40347 = 20450 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_40347 : ∀ j : Fin 20,
    40347 ≤ acceleratedOrbit j.val 40347 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_40347 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40347) = 531441 * m + 20450 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 40347
  rw [data_20_40347.1, data_20_40347.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_40347 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40347) < 1048576 * m + 40347 := by
  apply descent_of_endpoint
  · rw [data_20_40347.1]; exact data_20_40347.2.2
  · rw [data_20_40347.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 40447). -/
theorem data_20_40447 : oddCount 40447 20 = 12 ∧
    acceleratedOrbit 20 40447 = 20500 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_40447 : ∀ j : Fin 20,
    40447 ≤ acceleratedOrbit j.val 40447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_40447 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40447) = 531441 * m + 20500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 40447
  rw [data_20_40447.1, data_20_40447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_40447 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 40447) < 1048576 * m + 40447 := by
  apply descent_of_endpoint
  · rw [data_20_40447.1]; exact data_20_40447.2.2
  · rw [data_20_40447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 41455). -/
theorem data_20_41455 : oddCount 41455 20 = 12 ∧
    acceleratedOrbit 20 41455 = 21011 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_41455 : ∀ j : Fin 20,
    41455 ≤ acceleratedOrbit j.val 41455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_41455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 41455) = 531441 * m + 21011 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 41455
  rw [data_20_41455.1, data_20_41455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_41455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 41455) < 1048576 * m + 41455 := by
  apply descent_of_endpoint
  · rw [data_20_41455.1]; exact data_20_41455.2.2
  · rw [data_20_41455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 42495). -/
theorem data_20_42495 : oddCount 42495 20 = 12 ∧
    acceleratedOrbit 20 42495 = 21538 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_42495 : ∀ j : Fin 20,
    42495 ≤ acceleratedOrbit j.val 42495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_42495 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 42495) = 531441 * m + 21538 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 42495
  rw [data_20_42495.1, data_20_42495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_42495 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 42495) < 1048576 * m + 42495 := by
  apply descent_of_endpoint
  · rw [data_20_42495.1]; exact data_20_42495.2.2
  · rw [data_20_42495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 43003). -/
theorem data_20_43003 : oddCount 43003 20 = 12 ∧
    acceleratedOrbit 20 43003 = 21796 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_43003 : ∀ j : Fin 20,
    43003 ≤ acceleratedOrbit j.val 43003 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_43003 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 43003) = 531441 * m + 21796 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 43003
  rw [data_20_43003.1, data_20_43003.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_43003 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 43003) < 1048576 * m + 43003 := by
  apply descent_of_endpoint
  · rw [data_20_43003.1]; exact data_20_43003.2.2
  · rw [data_20_43003.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 44059). -/
theorem data_20_44059 : oddCount 44059 20 = 12 ∧
    acceleratedOrbit 20 44059 = 22331 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_44059 : ∀ j : Fin 20,
    44059 ≤ acceleratedOrbit j.val 44059 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_44059 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44059) = 531441 * m + 22331 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 44059
  rw [data_20_44059.1, data_20_44059.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_44059 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44059) < 1048576 * m + 44059 := by
  apply descent_of_endpoint
  · rw [data_20_44059.1]; exact data_20_44059.2.2
  · rw [data_20_44059.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 44199). -/
theorem data_20_44199 : oddCount 44199 20 = 12 ∧
    acceleratedOrbit 20 44199 = 22402 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_44199 : ∀ j : Fin 20,
    44199 ≤ acceleratedOrbit j.val 44199 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_44199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44199) = 531441 * m + 22402 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 44199
  rw [data_20_44199.1, data_20_44199.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_44199 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 44199) < 1048576 * m + 44199 := by
  apply descent_of_endpoint
  · rw [data_20_44199.1]; exact data_20_44199.2.2
  · rw [data_20_44199.2.1]; decide

end Collatz.Research.FirstDescent.Batch235
