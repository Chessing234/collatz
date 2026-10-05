import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 39. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch039
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 30767). -/
theorem data_15_30767 : oddCount 30767 15 = 9 ∧
    acceleratedOrbit 15 30767 = 18482 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_30767 : ∀ j : Fin 15,
    30767 ≤ acceleratedOrbit j.val 30767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_30767 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30767) = 19683 * m + 18482 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 30767
  rw [data_15_30767.1, data_15_30767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_30767 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30767) < 32768 * m + 30767 := by
  apply descent_of_endpoint
  · rw [data_15_30767.1]; exact data_15_30767.2.2
  · rw [data_15_30767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 30887). -/
theorem data_15_30887 : oddCount 30887 15 = 9 ∧
    acceleratedOrbit 15 30887 = 18554 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_30887 : ∀ j : Fin 15,
    30887 ≤ acceleratedOrbit j.val 30887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_30887 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30887) = 19683 * m + 18554 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 30887
  rw [data_15_30887.1, data_15_30887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_30887 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30887) < 32768 * m + 30887 := by
  apply descent_of_endpoint
  · rw [data_15_30887.1]; exact data_15_30887.2.2
  · rw [data_15_30887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 31711). -/
theorem data_15_31711 : oddCount 31711 15 = 9 ∧
    acceleratedOrbit 15 31711 = 19049 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_31711 : ∀ j : Fin 15,
    31711 ≤ acceleratedOrbit j.val 31711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_31711 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 31711) = 19683 * m + 19049 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 31711
  rw [data_15_31711.1, data_15_31711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_31711 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 31711) < 32768 * m + 31711 := by
  apply descent_of_endpoint
  · rw [data_15_31711.1]; exact data_15_31711.2.2
  · rw [data_15_31711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 31771). -/
theorem data_15_31771 : oddCount 31771 15 = 9 ∧
    acceleratedOrbit 15 31771 = 19085 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_31771 : ∀ j : Fin 15,
    31771 ≤ acceleratedOrbit j.val 31771 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_31771 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 31771) = 19683 * m + 19085 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 31771
  rw [data_15_31771.1, data_15_31771.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_31771 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 31771) < 32768 * m + 31771 := by
  apply descent_of_endpoint
  · rw [data_15_31771.1]; exact data_15_31771.2.2
  · rw [data_15_31771.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 31899). -/
theorem data_15_31899 : oddCount 31899 15 = 9 ∧
    acceleratedOrbit 15 31899 = 19162 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_31899 : ∀ j : Fin 15,
    31899 ≤ acceleratedOrbit j.val 31899 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_31899 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 31899) = 19683 * m + 19162 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 31899
  rw [data_15_31899.1, data_15_31899.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_31899 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 31899) < 32768 * m + 31899 := by
  apply descent_of_endpoint
  · rw [data_15_31899.1]; exact data_15_31899.2.2
  · rw [data_15_31899.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 32155). -/
theorem data_15_32155 : oddCount 32155 15 = 9 ∧
    acceleratedOrbit 15 32155 = 19316 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_32155 : ∀ j : Fin 15,
    32155 ≤ acceleratedOrbit j.val 32155 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_32155 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32155) = 19683 * m + 19316 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 32155
  rw [data_15_32155.1, data_15_32155.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_32155 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32155) < 32768 * m + 32155 := by
  apply descent_of_endpoint
  · rw [data_15_32155.1]; exact data_15_32155.2.2
  · rw [data_15_32155.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 32239). -/
theorem data_15_32239 : oddCount 32239 15 = 9 ∧
    acceleratedOrbit 15 32239 = 19366 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_32239 : ∀ j : Fin 15,
    32239 ≤ acceleratedOrbit j.val 32239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_32239 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32239) = 19683 * m + 19366 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 32239
  rw [data_15_32239.1, data_15_32239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_32239 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32239) < 32768 * m + 32239 := by
  apply descent_of_endpoint
  · rw [data_15_32239.1]; exact data_15_32239.2.2
  · rw [data_15_32239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 32575). -/
theorem data_15_32575 : oddCount 32575 15 = 9 ∧
    acceleratedOrbit 15 32575 = 19568 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_32575 : ∀ j : Fin 15,
    32575 ≤ acceleratedOrbit j.val 32575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_32575 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32575) = 19683 * m + 19568 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 32575
  rw [data_15_32575.1, data_15_32575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_32575 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32575) < 32768 * m + 32575 := by
  apply descent_of_endpoint
  · rw [data_15_32575.1]; exact data_15_32575.2.2
  · rw [data_15_32575.2.1]; decide

end Collatz.Research.FirstDescent.Batch039
