import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 230. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch230
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 25319). -/
theorem data_20_25319 : oddCount 25319 20 = 12 ∧
    acceleratedOrbit 20 25319 = 12833 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_25319 : ∀ j : Fin 20,
    25319 ≤ acceleratedOrbit j.val 25319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_25319 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 25319) = 531441 * m + 12833 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 25319
  rw [data_20_25319.1, data_20_25319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_25319 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 25319) < 1048576 * m + 25319 := by
  apply descent_of_endpoint
  · rw [data_20_25319.1]; exact data_20_25319.2.2
  · rw [data_20_25319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 25631). -/
theorem data_20_25631 : oddCount 25631 20 = 12 ∧
    acceleratedOrbit 20 25631 = 12991 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_25631 : ∀ j : Fin 20,
    25631 ≤ acceleratedOrbit j.val 25631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_25631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 25631) = 531441 * m + 12991 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 25631
  rw [data_20_25631.1, data_20_25631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_25631 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 25631) < 1048576 * m + 25631 := by
  apply descent_of_endpoint
  · rw [data_20_25631.1]; exact data_20_25631.2.2
  · rw [data_20_25631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 26319). -/
theorem data_20_26319 : oddCount 26319 20 = 12 ∧
    acceleratedOrbit 20 26319 = 13340 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_26319 : ∀ j : Fin 20,
    26319 ≤ acceleratedOrbit j.val 26319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_26319 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 26319) = 531441 * m + 13340 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 26319
  rw [data_20_26319.1, data_20_26319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_26319 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 26319) < 1048576 * m + 26319 := by
  apply descent_of_endpoint
  · rw [data_20_26319.1]; exact data_20_26319.2.2
  · rw [data_20_26319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 26495). -/
theorem data_20_26495 : oddCount 26495 20 = 12 ∧
    acceleratedOrbit 20 26495 = 13429 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_26495 : ∀ j : Fin 20,
    26495 ≤ acceleratedOrbit j.val 26495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_26495 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 26495) = 531441 * m + 13429 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 26495
  rw [data_20_26495.1, data_20_26495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_26495 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 26495) < 1048576 * m + 26495 := by
  apply descent_of_endpoint
  · rw [data_20_26495.1]; exact data_20_26495.2.2
  · rw [data_20_26495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 26875). -/
theorem data_20_26875 : oddCount 26875 20 = 12 ∧
    acceleratedOrbit 20 26875 = 13622 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_26875 : ∀ j : Fin 20,
    26875 ≤ acceleratedOrbit j.val 26875 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_26875 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 26875) = 531441 * m + 13622 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 26875
  rw [data_20_26875.1, data_20_26875.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_26875 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 26875) < 1048576 * m + 26875 := by
  apply descent_of_endpoint
  · rw [data_20_26875.1]; exact data_20_26875.2.2
  · rw [data_20_26875.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 27035). -/
theorem data_20_27035 : oddCount 27035 20 = 12 ∧
    acceleratedOrbit 20 27035 = 13703 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_27035 : ∀ j : Fin 20,
    27035 ≤ acceleratedOrbit j.val 27035 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_27035 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 27035) = 531441 * m + 13703 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 27035
  rw [data_20_27035.1, data_20_27035.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_27035 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 27035) < 1048576 * m + 27035 := by
  apply descent_of_endpoint
  · rw [data_20_27035.1]; exact data_20_27035.2.2
  · rw [data_20_27035.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 27391). -/
theorem data_20_27391 : oddCount 27391 20 = 12 ∧
    acceleratedOrbit 20 27391 = 13883 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_27391 : ∀ j : Fin 20,
    27391 ≤ acceleratedOrbit j.val 27391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_27391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 27391) = 531441 * m + 13883 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 27391
  rw [data_20_27391.1, data_20_27391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_27391 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 27391) < 1048576 * m + 27391 := by
  apply descent_of_endpoint
  · rw [data_20_27391.1]; exact data_20_27391.2.2
  · rw [data_20_27391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 27679). -/
theorem data_20_27679 : oddCount 27679 20 = 12 ∧
    acceleratedOrbit 20 27679 = 14029 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_27679 : ∀ j : Fin 20,
    27679 ≤ acceleratedOrbit j.val 27679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_27679 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 27679) = 531441 * m + 14029 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 27679
  rw [data_20_27679.1, data_20_27679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_27679 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 27679) < 1048576 * m + 27679 := by
  apply descent_of_endpoint
  · rw [data_20_27679.1]; exact data_20_27679.2.2
  · rw [data_20_27679.2.1]; decide

end Collatz.Research.FirstDescent.Batch230
