import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 55. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch055
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 16635). -/
theorem data_16_16635 : oddCount 16635 16 = 10 ∧
    acceleratedOrbit 16 16635 = 14990 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_16635 : ∀ j : Fin 16,
    16635 ≤ acceleratedOrbit j.val 16635 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_16635 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16635) = 59049 * m + 14990 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 16635
  rw [data_16_16635.1, data_16_16635.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_16635 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16635) < 65536 * m + 16635 := by
  apply descent_of_endpoint
  · rw [data_16_16635.1]; exact data_16_16635.2.2
  · rw [data_16_16635.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 16831). -/
theorem data_16_16831 : oddCount 16831 16 = 10 ∧
    acceleratedOrbit 16 16831 = 15166 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_16831 : ∀ j : Fin 16,
    16831 ≤ acceleratedOrbit j.val 16831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_16831 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16831) = 59049 * m + 15166 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 16831
  rw [data_16_16831.1, data_16_16831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_16831 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 16831) < 65536 * m + 16831 := by
  apply descent_of_endpoint
  · rw [data_16_16831.1]; exact data_16_16831.2.2
  · rw [data_16_16831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17055). -/
theorem data_16_17055 : oddCount 17055 16 = 10 ∧
    acceleratedOrbit 16 17055 = 15368 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17055 : ∀ j : Fin 16,
    17055 ≤ acceleratedOrbit j.val 17055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17055 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17055) = 59049 * m + 15368 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17055
  rw [data_16_17055.1, data_16_17055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17055 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17055) < 65536 * m + 17055 := by
  apply descent_of_endpoint
  · rw [data_16_17055.1]; exact data_16_17055.2.2
  · rw [data_16_17055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17127). -/
theorem data_16_17127 : oddCount 17127 16 = 10 ∧
    acceleratedOrbit 16 17127 = 15433 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17127 : ∀ j : Fin 16,
    17127 ≤ acceleratedOrbit j.val 17127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17127) = 59049 * m + 15433 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17127
  rw [data_16_17127.1, data_16_17127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17127) < 65536 * m + 17127 := by
  apply descent_of_endpoint
  · rw [data_16_17127.1]; exact data_16_17127.2.2
  · rw [data_16_17127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17135). -/
theorem data_16_17135 : oddCount 17135 16 = 10 ∧
    acceleratedOrbit 16 17135 = 15440 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17135 : ∀ j : Fin 16,
    17135 ≤ acceleratedOrbit j.val 17135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17135) = 59049 * m + 15440 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17135
  rw [data_16_17135.1, data_16_17135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17135 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17135) < 65536 * m + 17135 := by
  apply descent_of_endpoint
  · rw [data_16_17135.1]; exact data_16_17135.2.2
  · rw [data_16_17135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17223). -/
theorem data_16_17223 : oddCount 17223 16 = 10 ∧
    acceleratedOrbit 16 17223 = 15520 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17223 : ∀ j : Fin 16,
    17223 ≤ acceleratedOrbit j.val 17223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17223) = 59049 * m + 15520 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17223
  rw [data_16_17223.1, data_16_17223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17223 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17223) < 65536 * m + 17223 := by
  apply descent_of_endpoint
  · rw [data_16_17223.1]; exact data_16_17223.2.2
  · rw [data_16_17223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17311). -/
theorem data_16_17311 : oddCount 17311 16 = 10 ∧
    acceleratedOrbit 16 17311 = 15599 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17311 : ∀ j : Fin 16,
    17311 ≤ acceleratedOrbit j.val 17311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17311) = 59049 * m + 15599 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17311
  rw [data_16_17311.1, data_16_17311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17311 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17311) < 65536 * m + 17311 := by
  apply descent_of_endpoint
  · rw [data_16_17311.1]; exact data_16_17311.2.2
  · rw [data_16_17311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17391). -/
theorem data_16_17391 : oddCount 17391 16 = 10 ∧
    acceleratedOrbit 16 17391 = 15671 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17391 : ∀ j : Fin 16,
    17391 ≤ acceleratedOrbit j.val 17391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17391 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17391) = 59049 * m + 15671 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17391
  rw [data_16_17391.1, data_16_17391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17391 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17391) < 65536 * m + 17391 := by
  apply descent_of_endpoint
  · rw [data_16_17391.1]; exact data_16_17391.2.2
  · rw [data_16_17391.2.1]; decide

end Collatz.Research.FirstDescent.Batch055
