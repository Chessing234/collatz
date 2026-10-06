import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 274. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch274
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 164847). -/
theorem data_20_164847 : oddCount 164847 20 = 12 ∧
    acceleratedOrbit 20 164847 = 83549 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_164847 : ∀ j : Fin 20,
    164847 ≤ acceleratedOrbit j.val 164847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_164847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 164847) = 531441 * m + 83549 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 164847
  rw [data_20_164847.1, data_20_164847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_164847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 164847) < 1048576 * m + 164847 := by
  apply descent_of_endpoint
  · rw [data_20_164847.1]; exact data_20_164847.2.2
  · rw [data_20_164847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 164895). -/
theorem data_20_164895 : oddCount 164895 20 = 12 ∧
    acceleratedOrbit 20 164895 = 83573 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_164895 : ∀ j : Fin 20,
    164895 ≤ acceleratedOrbit j.val 164895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_164895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 164895) = 531441 * m + 83573 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 164895
  rw [data_20_164895.1, data_20_164895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_164895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 164895) < 1048576 * m + 164895 := by
  apply descent_of_endpoint
  · rw [data_20_164895.1]; exact data_20_164895.2.2
  · rw [data_20_164895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 165023). -/
theorem data_20_165023 : oddCount 165023 20 = 12 ∧
    acceleratedOrbit 20 165023 = 83638 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_165023 : ∀ j : Fin 20,
    165023 ≤ acceleratedOrbit j.val 165023 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_165023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 165023) = 531441 * m + 83638 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 165023
  rw [data_20_165023.1, data_20_165023.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_165023 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 165023) < 1048576 * m + 165023 := by
  apply descent_of_endpoint
  · rw [data_20_165023.1]; exact data_20_165023.2.2
  · rw [data_20_165023.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 165759). -/
theorem data_20_165759 : oddCount 165759 20 = 12 ∧
    acceleratedOrbit 20 165759 = 84011 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_165759 : ∀ j : Fin 20,
    165759 ≤ acceleratedOrbit j.val 165759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_165759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 165759) = 531441 * m + 84011 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 165759
  rw [data_20_165759.1, data_20_165759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_165759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 165759) < 1048576 * m + 165759 := by
  apply descent_of_endpoint
  · rw [data_20_165759.1]; exact data_20_165759.2.2
  · rw [data_20_165759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 166727). -/
theorem data_20_166727 : oddCount 166727 20 = 12 ∧
    acceleratedOrbit 20 166727 = 84502 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_166727 : ∀ j : Fin 20,
    166727 ≤ acceleratedOrbit j.val 166727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_166727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 166727) = 531441 * m + 84502 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 166727
  rw [data_20_166727.1, data_20_166727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_166727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 166727) < 1048576 * m + 166727 := by
  apply descent_of_endpoint
  · rw [data_20_166727.1]; exact data_20_166727.2.2
  · rw [data_20_166727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 167551). -/
theorem data_20_167551 : oddCount 167551 20 = 12 ∧
    acceleratedOrbit 20 167551 = 84919 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_167551 : ∀ j : Fin 20,
    167551 ≤ acceleratedOrbit j.val 167551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_167551 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 167551) = 531441 * m + 84919 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 167551
  rw [data_20_167551.1, data_20_167551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_167551 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 167551) < 1048576 * m + 167551 := by
  apply descent_of_endpoint
  · rw [data_20_167551.1]; exact data_20_167551.2.2
  · rw [data_20_167551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 167663). -/
theorem data_20_167663 : oddCount 167663 20 = 12 ∧
    acceleratedOrbit 20 167663 = 84976 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_167663 : ∀ j : Fin 20,
    167663 ≤ acceleratedOrbit j.val 167663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_167663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 167663) = 531441 * m + 84976 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 167663
  rw [data_20_167663.1, data_20_167663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_167663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 167663) < 1048576 * m + 167663 := by
  apply descent_of_endpoint
  · rw [data_20_167663.1]; exact data_20_167663.2.2
  · rw [data_20_167663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 167771). -/
theorem data_20_167771 : oddCount 167771 20 = 12 ∧
    acceleratedOrbit 20 167771 = 85031 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_167771 : ∀ j : Fin 20,
    167771 ≤ acceleratedOrbit j.val 167771 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_167771 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 167771) = 531441 * m + 85031 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 167771
  rw [data_20_167771.1, data_20_167771.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_167771 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 167771) < 1048576 * m + 167771 := by
  apply descent_of_endpoint
  · rw [data_20_167771.1]; exact data_20_167771.2.2
  · rw [data_20_167771.2.1]; decide

end Collatz.Research.FirstDescent.Batch274
