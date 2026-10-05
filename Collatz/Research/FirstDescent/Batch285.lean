import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 285. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch285
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 194799). -/
theorem data_20_194799 : oddCount 194799 20 = 12 ∧
    acceleratedOrbit 20 194799 = 98729 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_194799 : ∀ j : Fin 20,
    194799 ≤ acceleratedOrbit j.val 194799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_194799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 194799) = 531441 * m + 98729 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 194799
  rw [data_20_194799.1, data_20_194799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_194799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 194799) < 1048576 * m + 194799 := by
  apply descent_of_endpoint
  · rw [data_20_194799.1]; exact data_20_194799.2.2
  · rw [data_20_194799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 195175). -/
theorem data_20_195175 : oddCount 195175 20 = 12 ∧
    acceleratedOrbit 20 195175 = 98920 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_195175 : ∀ j : Fin 20,
    195175 ≤ acceleratedOrbit j.val 195175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_195175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195175) = 531441 * m + 98920 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 195175
  rw [data_20_195175.1, data_20_195175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_195175 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195175) < 1048576 * m + 195175 := by
  apply descent_of_endpoint
  · rw [data_20_195175.1]; exact data_20_195175.2.2
  · rw [data_20_195175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 195355). -/
theorem data_20_195355 : oddCount 195355 20 = 12 ∧
    acceleratedOrbit 20 195355 = 99011 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_195355 : ∀ j : Fin 20,
    195355 ≤ acceleratedOrbit j.val 195355 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_195355 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195355) = 531441 * m + 99011 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 195355
  rw [data_20_195355.1, data_20_195355.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_195355 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195355) < 1048576 * m + 195355 := by
  apply descent_of_endpoint
  · rw [data_20_195355.1]; exact data_20_195355.2.2
  · rw [data_20_195355.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 195823). -/
theorem data_20_195823 : oddCount 195823 20 = 12 ∧
    acceleratedOrbit 20 195823 = 99248 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_195823 : ∀ j : Fin 20,
    195823 ≤ acceleratedOrbit j.val 195823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_195823 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195823) = 531441 * m + 99248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 195823
  rw [data_20_195823.1, data_20_195823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_195823 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195823) < 1048576 * m + 195823 := by
  apply descent_of_endpoint
  · rw [data_20_195823.1]; exact data_20_195823.2.2
  · rw [data_20_195823.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 195839). -/
theorem data_20_195839 : oddCount 195839 20 = 12 ∧
    acceleratedOrbit 20 195839 = 99256 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_195839 : ∀ j : Fin 20,
    195839 ≤ acceleratedOrbit j.val 195839 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_195839 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195839) = 531441 * m + 99256 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 195839
  rw [data_20_195839.1, data_20_195839.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_195839 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 195839) < 1048576 * m + 195839 := by
  apply descent_of_endpoint
  · rw [data_20_195839.1]; exact data_20_195839.2.2
  · rw [data_20_195839.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 196063). -/
theorem data_20_196063 : oddCount 196063 20 = 12 ∧
    acceleratedOrbit 20 196063 = 99370 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_196063 : ∀ j : Fin 20,
    196063 ≤ acceleratedOrbit j.val 196063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_196063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196063) = 531441 * m + 99370 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 196063
  rw [data_20_196063.1, data_20_196063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_196063 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196063) < 1048576 * m + 196063 := by
  apply descent_of_endpoint
  · rw [data_20_196063.1]; exact data_20_196063.2.2
  · rw [data_20_196063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 196543). -/
theorem data_20_196543 : oddCount 196543 20 = 12 ∧
    acceleratedOrbit 20 196543 = 99613 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_196543 : ∀ j : Fin 20,
    196543 ≤ acceleratedOrbit j.val 196543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_196543 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196543) = 531441 * m + 99613 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 196543
  rw [data_20_196543.1, data_20_196543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_196543 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196543) < 1048576 * m + 196543 := by
  apply descent_of_endpoint
  · rw [data_20_196543.1]; exact data_20_196543.2.2
  · rw [data_20_196543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 196603). -/
theorem data_20_196603 : oddCount 196603 20 = 12 ∧
    acceleratedOrbit 20 196603 = 99644 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_196603 : ∀ j : Fin 20,
    196603 ≤ acceleratedOrbit j.val 196603 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_196603 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196603) = 531441 * m + 99644 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 196603
  rw [data_20_196603.1, data_20_196603.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_196603 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 196603) < 1048576 * m + 196603 := by
  apply descent_of_endpoint
  · rw [data_20_196603.1]; exact data_20_196603.2.2
  · rw [data_20_196603.2.1]; decide

end Collatz.Research.FirstDescent.Batch285
