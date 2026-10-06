import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 263. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch263
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 129383). -/
theorem data_20_129383 : oddCount 129383 20 = 12 ∧
    acceleratedOrbit 20 129383 = 65575 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_129383 : ∀ j : Fin 20,
    129383 ≤ acceleratedOrbit j.val 129383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_129383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 129383) = 531441 * m + 65575 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 129383
  rw [data_20_129383.1, data_20_129383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_129383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 129383) < 1048576 * m + 129383 := by
  apply descent_of_endpoint
  · rw [data_20_129383.1]; exact data_20_129383.2.2
  · rw [data_20_129383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 129639). -/
theorem data_20_129639 : oddCount 129639 20 = 12 ∧
    acceleratedOrbit 20 129639 = 65705 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_129639 : ∀ j : Fin 20,
    129639 ≤ acceleratedOrbit j.val 129639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_129639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 129639) = 531441 * m + 65705 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 129639
  rw [data_20_129639.1, data_20_129639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_129639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 129639) < 1048576 * m + 129639 := by
  apply descent_of_endpoint
  · rw [data_20_129639.1]; exact data_20_129639.2.2
  · rw [data_20_129639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 130527). -/
theorem data_20_130527 : oddCount 130527 20 = 12 ∧
    acceleratedOrbit 20 130527 = 66155 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_130527 : ∀ j : Fin 20,
    130527 ≤ acceleratedOrbit j.val 130527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_130527 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 130527) = 531441 * m + 66155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 130527
  rw [data_20_130527.1, data_20_130527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_130527 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 130527) < 1048576 * m + 130527 := by
  apply descent_of_endpoint
  · rw [data_20_130527.1]; exact data_20_130527.2.2
  · rw [data_20_130527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 131007). -/
theorem data_20_131007 : oddCount 131007 20 = 12 ∧
    acceleratedOrbit 20 131007 = 66398 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_131007 : ∀ j : Fin 20,
    131007 ≤ acceleratedOrbit j.val 131007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_131007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131007) = 531441 * m + 66398 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 131007
  rw [data_20_131007.1, data_20_131007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_131007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131007) < 1048576 * m + 131007 := by
  apply descent_of_endpoint
  · rw [data_20_131007.1]; exact data_20_131007.2.2
  · rw [data_20_131007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 131135). -/
theorem data_20_131135 : oddCount 131135 20 = 12 ∧
    acceleratedOrbit 20 131135 = 66463 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_131135 : ∀ j : Fin 20,
    131135 ≤ acceleratedOrbit j.val 131135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_131135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131135) = 531441 * m + 66463 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 131135
  rw [data_20_131135.1, data_20_131135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_131135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131135) < 1048576 * m + 131135 := by
  apply descent_of_endpoint
  · rw [data_20_131135.1]; exact data_20_131135.2.2
  · rw [data_20_131135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 131295). -/
theorem data_20_131295 : oddCount 131295 20 = 12 ∧
    acceleratedOrbit 20 131295 = 66544 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_131295 : ∀ j : Fin 20,
    131295 ≤ acceleratedOrbit j.val 131295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_131295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131295) = 531441 * m + 66544 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 131295
  rw [data_20_131295.1, data_20_131295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_131295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131295) < 1048576 * m + 131295 := by
  apply descent_of_endpoint
  · rw [data_20_131295.1]; exact data_20_131295.2.2
  · rw [data_20_131295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 131739). -/
theorem data_20_131739 : oddCount 131739 20 = 12 ∧
    acceleratedOrbit 20 131739 = 66769 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_131739 : ∀ j : Fin 20,
    131739 ≤ acceleratedOrbit j.val 131739 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_131739 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131739) = 531441 * m + 66769 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 131739
  rw [data_20_131739.1, data_20_131739.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_131739 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 131739) < 1048576 * m + 131739 := by
  apply descent_of_endpoint
  · rw [data_20_131739.1]; exact data_20_131739.2.2
  · rw [data_20_131739.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 132455). -/
theorem data_20_132455 : oddCount 132455 20 = 12 ∧
    acceleratedOrbit 20 132455 = 67132 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_132455 : ∀ j : Fin 20,
    132455 ≤ acceleratedOrbit j.val 132455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_132455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 132455) = 531441 * m + 67132 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 132455
  rw [data_20_132455.1, data_20_132455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_132455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 132455) < 1048576 * m + 132455 := by
  apply descent_of_endpoint
  · rw [data_20_132455.1]; exact data_20_132455.2.2
  · rw [data_20_132455.2.1]; decide

end Collatz.Research.FirstDescent.Batch263
