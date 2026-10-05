import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 286. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch286
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 196763). -/
theorem data_20_196763 : oddCount 196763 20 = 12 ∧
    acceleratedOrbit 20 196763 = 99725 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_196763 : ∀ j : Fin 20,
    196763 ≤ acceleratedOrbit j.val 196763 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_196763 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196763) = 531441 * m + 99725 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 196763
  rw [data_20_196763.1, data_20_196763.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_196763 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196763) < 1048576 * m + 196763 := by
  apply descent_of_endpoint
  · rw [data_20_196763.1]; exact data_20_196763.2.2
  · rw [data_20_196763.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 197279). -/
theorem data_20_197279 : oddCount 197279 20 = 12 ∧
    acceleratedOrbit 20 197279 = 99986 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_197279 : ∀ j : Fin 20,
    197279 ≤ acceleratedOrbit j.val 197279 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_197279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 197279) = 531441 * m + 99986 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 197279
  rw [data_20_197279.1, data_20_197279.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_197279 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 197279) < 1048576 * m + 197279 := by
  apply descent_of_endpoint
  · rw [data_20_197279.1]; exact data_20_197279.2.2
  · rw [data_20_197279.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 197403). -/
theorem data_20_197403 : oddCount 197403 20 = 12 ∧
    acceleratedOrbit 20 197403 = 100049 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_197403 : ∀ j : Fin 20,
    197403 ≤ acceleratedOrbit j.val 197403 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_197403 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 197403) = 531441 * m + 100049 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 197403
  rw [data_20_197403.1, data_20_197403.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_197403 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 197403) < 1048576 * m + 197403 := by
  apply descent_of_endpoint
  · rw [data_20_197403.1]; exact data_20_197403.2.2
  · rw [data_20_197403.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 197887). -/
theorem data_20_197887 : oddCount 197887 20 = 12 ∧
    acceleratedOrbit 20 197887 = 100294 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_197887 : ∀ j : Fin 20,
    197887 ≤ acceleratedOrbit j.val 197887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_197887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 197887) = 531441 * m + 100294 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 197887
  rw [data_20_197887.1, data_20_197887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_197887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 197887) < 1048576 * m + 197887 := by
  apply descent_of_endpoint
  · rw [data_20_197887.1]; exact data_20_197887.2.2
  · rw [data_20_197887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 198095). -/
theorem data_20_198095 : oddCount 198095 20 = 12 ∧
    acceleratedOrbit 20 198095 = 100400 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_198095 : ∀ j : Fin 20,
    198095 ≤ acceleratedOrbit j.val 198095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_198095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 198095) = 531441 * m + 100400 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 198095
  rw [data_20_198095.1, data_20_198095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_198095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 198095) < 1048576 * m + 198095 := by
  apply descent_of_endpoint
  · rw [data_20_198095.1]; exact data_20_198095.2.2
  · rw [data_20_198095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 198303). -/
theorem data_20_198303 : oddCount 198303 20 = 12 ∧
    acceleratedOrbit 20 198303 = 100505 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_198303 : ∀ j : Fin 20,
    198303 ≤ acceleratedOrbit j.val 198303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_198303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 198303) = 531441 * m + 100505 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 198303
  rw [data_20_198303.1, data_20_198303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_198303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 198303) < 1048576 * m + 198303 := by
  apply descent_of_endpoint
  · rw [data_20_198303.1]; exact data_20_198303.2.2
  · rw [data_20_198303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 199143). -/
theorem data_20_199143 : oddCount 199143 20 = 12 ∧
    acceleratedOrbit 20 199143 = 100931 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_199143 : ∀ j : Fin 20,
    199143 ≤ acceleratedOrbit j.val 199143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_199143 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199143) = 531441 * m + 100931 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 199143
  rw [data_20_199143.1, data_20_199143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_199143 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199143) < 1048576 * m + 199143 := by
  apply descent_of_endpoint
  · rw [data_20_199143.1]; exact data_20_199143.2.2
  · rw [data_20_199143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 199259). -/
theorem data_20_199259 : oddCount 199259 20 = 12 ∧
    acceleratedOrbit 20 199259 = 100990 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_199259 : ∀ j : Fin 20,
    199259 ≤ acceleratedOrbit j.val 199259 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_199259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199259) = 531441 * m + 100990 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 199259
  rw [data_20_199259.1, data_20_199259.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_199259 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199259) < 1048576 * m + 199259 := by
  apply descent_of_endpoint
  · rw [data_20_199259.1]; exact data_20_199259.2.2
  · rw [data_20_199259.2.1]; decide

end Collatz.Research.FirstDescent.Batch286
