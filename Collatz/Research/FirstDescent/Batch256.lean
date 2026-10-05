import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 256. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch256
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 102683). -/
theorem data_20_102683 : oddCount 102683 20 = 12 ∧
    acceleratedOrbit 20 102683 = 52043 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_102683 : ∀ j : Fin 20,
    102683 ≤ acceleratedOrbit j.val 102683 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_102683 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 102683) = 531441 * m + 52043 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 102683
  rw [data_20_102683.1, data_20_102683.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_102683 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 102683) < 1048576 * m + 102683 := by
  apply descent_of_endpoint
  · rw [data_20_102683.1]; exact data_20_102683.2.2
  · rw [data_20_102683.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 103039). -/
theorem data_20_103039 : oddCount 103039 20 = 12 ∧
    acceleratedOrbit 20 103039 = 52223 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_103039 : ∀ j : Fin 20,
    103039 ≤ acceleratedOrbit j.val 103039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_103039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 103039) = 531441 * m + 52223 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 103039
  rw [data_20_103039.1, data_20_103039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_103039 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 103039) < 1048576 * m + 103039 := by
  apply descent_of_endpoint
  · rw [data_20_103039.1]; exact data_20_103039.2.2
  · rw [data_20_103039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 103119). -/
theorem data_20_103119 : oddCount 103119 20 = 12 ∧
    acceleratedOrbit 20 103119 = 52264 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_103119 : ∀ j : Fin 20,
    103119 ≤ acceleratedOrbit j.val 103119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_103119 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 103119) = 531441 * m + 52264 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 103119
  rw [data_20_103119.1, data_20_103119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_103119 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 103119) < 1048576 * m + 103119 := by
  apply descent_of_endpoint
  · rw [data_20_103119.1]; exact data_20_103119.2.2
  · rw [data_20_103119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 103451). -/
theorem data_20_103451 : oddCount 103451 20 = 12 ∧
    acceleratedOrbit 20 103451 = 52432 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_103451 : ∀ j : Fin 20,
    103451 ≤ acceleratedOrbit j.val 103451 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_103451 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 103451) = 531441 * m + 52432 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 103451
  rw [data_20_103451.1, data_20_103451.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_103451 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 103451) < 1048576 * m + 103451 := by
  apply descent_of_endpoint
  · rw [data_20_103451.1]; exact data_20_103451.2.2
  · rw [data_20_103451.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 104167). -/
theorem data_20_104167 : oddCount 104167 20 = 12 ∧
    acceleratedOrbit 20 104167 = 52795 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_104167 : ∀ j : Fin 20,
    104167 ≤ acceleratedOrbit j.val 104167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_104167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 104167) = 531441 * m + 52795 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 104167
  rw [data_20_104167.1, data_20_104167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_104167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 104167) < 1048576 * m + 104167 := by
  apply descent_of_endpoint
  · rw [data_20_104167.1]; exact data_20_104167.2.2
  · rw [data_20_104167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 104859). -/
theorem data_20_104859 : oddCount 104859 20 = 12 ∧
    acceleratedOrbit 20 104859 = 53146 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_104859 : ∀ j : Fin 20,
    104859 ≤ acceleratedOrbit j.val 104859 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_104859 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 104859) = 531441 * m + 53146 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 104859
  rw [data_20_104859.1, data_20_104859.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_104859 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 104859) < 1048576 * m + 104859 := by
  apply descent_of_endpoint
  · rw [data_20_104859.1]; exact data_20_104859.2.2
  · rw [data_20_104859.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 104927). -/
theorem data_20_104927 : oddCount 104927 20 = 12 ∧
    acceleratedOrbit 20 104927 = 53180 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_104927 : ∀ j : Fin 20,
    104927 ≤ acceleratedOrbit j.val 104927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_104927 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 104927) = 531441 * m + 53180 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 104927
  rw [data_20_104927.1, data_20_104927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_104927 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 104927) < 1048576 * m + 104927 := by
  apply descent_of_endpoint
  · rw [data_20_104927.1]; exact data_20_104927.2.2
  · rw [data_20_104927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 105755). -/
theorem data_20_105755 : oddCount 105755 20 = 12 ∧
    acceleratedOrbit 20 105755 = 53600 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_105755 : ∀ j : Fin 20,
    105755 ≤ acceleratedOrbit j.val 105755 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_105755 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 105755) = 531441 * m + 53600 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 105755
  rw [data_20_105755.1, data_20_105755.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_105755 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 105755) < 1048576 * m + 105755 := by
  apply descent_of_endpoint
  · rw [data_20_105755.1]; exact data_20_105755.2.2
  · rw [data_20_105755.2.1]; decide

end Collatz.Research.FirstDescent.Batch256
