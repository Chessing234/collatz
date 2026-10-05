import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 247. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch247
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 74719). -/
theorem data_20_74719 : oddCount 74719 20 = 12 ∧
    acceleratedOrbit 20 74719 = 37870 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_74719 : ∀ j : Fin 20,
    74719 ≤ acceleratedOrbit j.val 74719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_74719 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74719) = 531441 * m + 37870 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 74719
  rw [data_20_74719.1, data_20_74719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_74719 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74719) < 1048576 * m + 74719 := by
  apply descent_of_endpoint
  · rw [data_20_74719.1]; exact data_20_74719.2.2
  · rw [data_20_74719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 74751). -/
theorem data_20_74751 : oddCount 74751 20 = 12 ∧
    acceleratedOrbit 20 74751 = 37886 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_74751 : ∀ j : Fin 20,
    74751 ≤ acceleratedOrbit j.val 74751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_74751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74751) = 531441 * m + 37886 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 74751
  rw [data_20_74751.1, data_20_74751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_74751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74751) < 1048576 * m + 74751 := by
  apply descent_of_endpoint
  · rw [data_20_74751.1]; exact data_20_74751.2.2
  · rw [data_20_74751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 74879). -/
theorem data_20_74879 : oddCount 74879 20 = 12 ∧
    acceleratedOrbit 20 74879 = 37951 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_74879 : ∀ j : Fin 20,
    74879 ≤ acceleratedOrbit j.val 74879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_74879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74879) = 531441 * m + 37951 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 74879
  rw [data_20_74879.1, data_20_74879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_74879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 74879) < 1048576 * m + 74879 := by
  apply descent_of_endpoint
  · rw [data_20_74879.1]; exact data_20_74879.2.2
  · rw [data_20_74879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 75239). -/
theorem data_20_75239 : oddCount 75239 20 = 12 ∧
    acceleratedOrbit 20 75239 = 38134 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_75239 : ∀ j : Fin 20,
    75239 ≤ acceleratedOrbit j.val 75239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_75239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 75239) = 531441 * m + 38134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 75239
  rw [data_20_75239.1, data_20_75239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_75239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 75239) < 1048576 * m + 75239 := by
  apply descent_of_endpoint
  · rw [data_20_75239.1]; exact data_20_75239.2.2
  · rw [data_20_75239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 75879). -/
theorem data_20_75879 : oddCount 75879 20 = 12 ∧
    acceleratedOrbit 20 75879 = 38458 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_75879 : ∀ j : Fin 20,
    75879 ≤ acceleratedOrbit j.val 75879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_75879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 75879) = 531441 * m + 38458 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 75879
  rw [data_20_75879.1, data_20_75879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_75879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 75879) < 1048576 * m + 75879 := by
  apply descent_of_endpoint
  · rw [data_20_75879.1]; exact data_20_75879.2.2
  · rw [data_20_75879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 75887). -/
theorem data_20_75887 : oddCount 75887 20 = 12 ∧
    acceleratedOrbit 20 75887 = 38462 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_75887 : ∀ j : Fin 20,
    75887 ≤ acceleratedOrbit j.val 75887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_75887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 75887) = 531441 * m + 38462 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 75887
  rw [data_20_75887.1, data_20_75887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_75887 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 75887) < 1048576 * m + 75887 := by
  apply descent_of_endpoint
  · rw [data_20_75887.1]; exact data_20_75887.2.2
  · rw [data_20_75887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 76455). -/
theorem data_20_76455 : oddCount 76455 20 = 12 ∧
    acceleratedOrbit 20 76455 = 38750 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_76455 : ∀ j : Fin 20,
    76455 ≤ acceleratedOrbit j.val 76455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_76455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 76455) = 531441 * m + 38750 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 76455
  rw [data_20_76455.1, data_20_76455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_76455 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 76455) < 1048576 * m + 76455 := by
  apply descent_of_endpoint
  · rw [data_20_76455.1]; exact data_20_76455.2.2
  · rw [data_20_76455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 77467). -/
theorem data_20_77467 : oddCount 77467 20 = 12 ∧
    acceleratedOrbit 20 77467 = 39263 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_77467 : ∀ j : Fin 20,
    77467 ≤ acceleratedOrbit j.val 77467 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_77467 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 77467) = 531441 * m + 39263 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 77467
  rw [data_20_77467.1, data_20_77467.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_77467 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 77467) < 1048576 * m + 77467 := by
  apply descent_of_endpoint
  · rw [data_20_77467.1]; exact data_20_77467.2.2
  · rw [data_20_77467.2.1]; decide

end Collatz.Research.FirstDescent.Batch247
