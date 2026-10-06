import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 100. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch100
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 1791). -/
theorem data_18_1791 : oddCount 1791 18 = 11 ∧
    acceleratedOrbit 18 1791 = 1211 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_1791 : ∀ j : Fin 18,
    1791 ≤ acceleratedOrbit j.val 1791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_1791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1791) = 177147 * m + 1211 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 1791
  rw [data_18_1791.1, data_18_1791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_1791 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1791) < 262144 * m + 1791 := by
  apply descent_of_endpoint
  · rw [data_18_1791.1]; exact data_18_1791.2.2
  · rw [data_18_1791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 1883). -/
theorem data_18_1883 : oddCount 1883 18 = 11 ∧
    acceleratedOrbit 18 1883 = 1274 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_1883 : ∀ j : Fin 18,
    1883 ≤ acceleratedOrbit j.val 1883 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_1883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1883) = 177147 * m + 1274 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 1883
  rw [data_18_1883.1, data_18_1883.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_1883 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 1883) < 262144 * m + 1883 := by
  apply descent_of_endpoint
  · rw [data_18_1883.1]; exact data_18_1883.2.2
  · rw [data_18_1883.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 2043). -/
theorem data_18_2043 : oddCount 2043 18 = 11 ∧
    acceleratedOrbit 18 2043 = 1382 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_2043 : ∀ j : Fin 18,
    2043 ≤ acceleratedOrbit j.val 2043 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_2043 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2043) = 177147 * m + 1382 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 2043
  rw [data_18_2043.1, data_18_2043.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_2043 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2043) < 262144 * m + 2043 := by
  apply descent_of_endpoint
  · rw [data_18_2043.1]; exact data_18_2043.2.2
  · rw [data_18_2043.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 2159). -/
theorem data_18_2159 : oddCount 2159 18 = 11 ∧
    acceleratedOrbit 18 2159 = 1460 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_2159 : ∀ j : Fin 18,
    2159 ≤ acceleratedOrbit j.val 2159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_2159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2159) = 177147 * m + 1460 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 2159
  rw [data_18_2159.1, data_18_2159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_2159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2159) < 262144 * m + 2159 := by
  apply descent_of_endpoint
  · rw [data_18_2159.1]; exact data_18_2159.2.2
  · rw [data_18_2159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 2459). -/
theorem data_18_2459 : oddCount 2459 18 = 11 ∧
    acceleratedOrbit 18 2459 = 1663 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_2459 : ∀ j : Fin 18,
    2459 ≤ acceleratedOrbit j.val 2459 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_2459 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2459) = 177147 * m + 1663 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 2459
  rw [data_18_2459.1, data_18_2459.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_2459 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2459) < 262144 * m + 2459 := by
  apply descent_of_endpoint
  · rw [data_18_2459.1]; exact data_18_2459.2.2
  · rw [data_18_2459.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 2651). -/
theorem data_18_2651 : oddCount 2651 18 = 11 ∧
    acceleratedOrbit 18 2651 = 1793 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_2651 : ∀ j : Fin 18,
    2651 ≤ acceleratedOrbit j.val 2651 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_2651 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2651) = 177147 * m + 1793 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 2651
  rw [data_18_2651.1, data_18_2651.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_2651 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2651) < 262144 * m + 2651 := by
  apply descent_of_endpoint
  · rw [data_18_2651.1]; exact data_18_2651.2.2
  · rw [data_18_2651.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 2811). -/
theorem data_18_2811 : oddCount 2811 18 = 11 ∧
    acceleratedOrbit 18 2811 = 1901 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_2811 : ∀ j : Fin 18,
    2811 ≤ acceleratedOrbit j.val 2811 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_2811 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2811) = 177147 * m + 1901 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 2811
  rw [data_18_2811.1, data_18_2811.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_2811 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 2811) < 262144 * m + 2811 := by
  apply descent_of_endpoint
  · rw [data_18_2811.1]; exact data_18_2811.2.2
  · rw [data_18_2811.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 3183). -/
theorem data_18_3183 : oddCount 3183 18 = 11 ∧
    acceleratedOrbit 18 3183 = 2152 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_3183 : ∀ j : Fin 18,
    3183 ≤ acceleratedOrbit j.val 3183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_3183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3183) = 177147 * m + 2152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 3183
  rw [data_18_3183.1, data_18_3183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_3183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 3183) < 262144 * m + 3183 := by
  apply descent_of_endpoint
  · rw [data_18_3183.1]; exact data_18_3183.2.2
  · rw [data_18_3183.2.1]; decide

end Collatz.Research.FirstDescent.Batch100
