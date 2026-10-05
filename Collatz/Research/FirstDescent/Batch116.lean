import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 116. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch116
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 34907). -/
theorem data_18_34907 : oddCount 34907 18 = 11 ∧
    acceleratedOrbit 18 34907 = 23590 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_34907 : ∀ j : Fin 18,
    34907 ≤ acceleratedOrbit j.val 34907 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_34907 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34907) = 177147 * m + 23590 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 34907
  rw [data_18_34907.1, data_18_34907.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_34907 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34907) < 262144 * m + 34907 := by
  apply descent_of_endpoint
  · rw [data_18_34907.1]; exact data_18_34907.2.2
  · rw [data_18_34907.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 34943). -/
theorem data_18_34943 : oddCount 34943 18 = 11 ∧
    acceleratedOrbit 18 34943 = 23614 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_34943 : ∀ j : Fin 18,
    34943 ≤ acceleratedOrbit j.val 34943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_34943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34943) = 177147 * m + 23614 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 34943
  rw [data_18_34943.1, data_18_34943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_34943 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 34943) < 262144 * m + 34943 := by
  apply descent_of_endpoint
  · rw [data_18_34943.1]; exact data_18_34943.2.2
  · rw [data_18_34943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 35135). -/
theorem data_18_35135 : oddCount 35135 18 = 11 ∧
    acceleratedOrbit 18 35135 = 23744 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_35135 : ∀ j : Fin 18,
    35135 ≤ acceleratedOrbit j.val 35135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_35135 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 35135) = 177147 * m + 23744 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 35135
  rw [data_18_35135.1, data_18_35135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_35135 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 35135) < 262144 * m + 35135 := by
  apply descent_of_endpoint
  · rw [data_18_35135.1]; exact data_18_35135.2.2
  · rw [data_18_35135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 35175). -/
theorem data_18_35175 : oddCount 35175 18 = 11 ∧
    acceleratedOrbit 18 35175 = 23771 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_35175 : ∀ j : Fin 18,
    35175 ≤ acceleratedOrbit j.val 35175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_35175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 35175) = 177147 * m + 23771 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 35175
  rw [data_18_35175.1, data_18_35175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_35175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 35175) < 262144 * m + 35175 := by
  apply descent_of_endpoint
  · rw [data_18_35175.1]; exact data_18_35175.2.2
  · rw [data_18_35175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 35455). -/
theorem data_18_35455 : oddCount 35455 18 = 11 ∧
    acceleratedOrbit 18 35455 = 23960 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_35455 : ∀ j : Fin 18,
    35455 ≤ acceleratedOrbit j.val 35455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_35455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 35455) = 177147 * m + 23960 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 35455
  rw [data_18_35455.1, data_18_35455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_35455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 35455) < 262144 * m + 35455 := by
  apply descent_of_endpoint
  · rw [data_18_35455.1]; exact data_18_35455.2.2
  · rw [data_18_35455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 37403). -/
theorem data_18_37403 : oddCount 37403 18 = 11 ∧
    acceleratedOrbit 18 37403 = 25277 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_37403 : ∀ j : Fin 18,
    37403 ≤ acceleratedOrbit j.val 37403 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_37403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 37403) = 177147 * m + 25277 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 37403
  rw [data_18_37403.1, data_18_37403.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_37403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 37403) < 262144 * m + 37403 := by
  apply descent_of_endpoint
  · rw [data_18_37403.1]; exact data_18_37403.2.2
  · rw [data_18_37403.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 37759). -/
theorem data_18_37759 : oddCount 37759 18 = 11 ∧
    acceleratedOrbit 18 37759 = 25517 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_37759 : ∀ j : Fin 18,
    37759 ≤ acceleratedOrbit j.val 37759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_37759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 37759) = 177147 * m + 25517 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 37759
  rw [data_18_37759.1, data_18_37759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_37759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 37759) < 262144 * m + 37759 := by
  apply descent_of_endpoint
  · rw [data_18_37759.1]; exact data_18_37759.2.2
  · rw [data_18_37759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 37979). -/
theorem data_18_37979 : oddCount 37979 18 = 11 ∧
    acceleratedOrbit 18 37979 = 25666 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_37979 : ∀ j : Fin 18,
    37979 ≤ acceleratedOrbit j.val 37979 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_37979 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 37979) = 177147 * m + 25666 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 37979
  rw [data_18_37979.1, data_18_37979.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_37979 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 37979) < 262144 * m + 37979 := by
  apply descent_of_endpoint
  · rw [data_18_37979.1]; exact data_18_37979.2.2
  · rw [data_18_37979.2.1]; decide

end Collatz.Research.FirstDescent.Batch116
