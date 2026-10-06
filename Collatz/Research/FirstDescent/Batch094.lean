import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 94. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch094
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 59647). -/
theorem data_16_59647 : oddCount 59647 16 = 10 ∧
    acceleratedOrbit 16 59647 = 53744 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_59647 : ∀ j : Fin 16,
    59647 ≤ acceleratedOrbit j.val 59647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_59647 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59647) = 59049 * m + 53744 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 59647
  rw [data_16_59647.1, data_16_59647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_59647 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 59647) < 65536 * m + 59647 := by
  apply descent_of_endpoint
  · rw [data_16_59647.1]; exact data_16_59647.2.2
  · rw [data_16_59647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60015). -/
theorem data_16_60015 : oddCount 60015 16 = 10 ∧
    acceleratedOrbit 16 60015 = 54076 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60015 : ∀ j : Fin 16,
    60015 ≤ acceleratedOrbit j.val 60015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60015) = 59049 * m + 54076 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60015
  rw [data_16_60015.1, data_16_60015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60015) < 65536 * m + 60015 := by
  apply descent_of_endpoint
  · rw [data_16_60015.1]; exact data_16_60015.2.2
  · rw [data_16_60015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60063). -/
theorem data_16_60063 : oddCount 60063 16 = 10 ∧
    acceleratedOrbit 16 60063 = 54119 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60063 : ∀ j : Fin 16,
    60063 ≤ acceleratedOrbit j.val 60063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60063 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60063) = 59049 * m + 54119 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60063
  rw [data_16_60063.1, data_16_60063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60063 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60063) < 65536 * m + 60063 := by
  apply descent_of_endpoint
  · rw [data_16_60063.1]; exact data_16_60063.2.2
  · rw [data_16_60063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60143). -/
theorem data_16_60143 : oddCount 60143 16 = 10 ∧
    acceleratedOrbit 16 60143 = 54191 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60143 : ∀ j : Fin 16,
    60143 ≤ acceleratedOrbit j.val 60143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60143) = 59049 * m + 54191 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60143
  rw [data_16_60143.1, data_16_60143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60143) < 65536 * m + 60143 := by
  apply descent_of_endpoint
  · rw [data_16_60143.1]; exact data_16_60143.2.2
  · rw [data_16_60143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60231). -/
theorem data_16_60231 : oddCount 60231 16 = 10 ∧
    acceleratedOrbit 16 60231 = 54271 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60231 : ∀ j : Fin 16,
    60231 ≤ acceleratedOrbit j.val 60231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60231) = 59049 * m + 54271 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60231
  rw [data_16_60231.1, data_16_60231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60231) < 65536 * m + 60231 := by
  apply descent_of_endpoint
  · rw [data_16_60231.1]; exact data_16_60231.2.2
  · rw [data_16_60231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60271). -/
theorem data_16_60271 : oddCount 60271 16 = 10 ∧
    acceleratedOrbit 16 60271 = 54307 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60271 : ∀ j : Fin 16,
    60271 ≤ acceleratedOrbit j.val 60271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60271) = 59049 * m + 54307 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60271
  rw [data_16_60271.1, data_16_60271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60271) < 65536 * m + 60271 := by
  apply descent_of_endpoint
  · rw [data_16_60271.1]; exact data_16_60271.2.2
  · rw [data_16_60271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60571). -/
theorem data_16_60571 : oddCount 60571 16 = 10 ∧
    acceleratedOrbit 16 60571 = 54577 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60571 : ∀ j : Fin 16,
    60571 ≤ acceleratedOrbit j.val 60571 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60571 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60571) = 59049 * m + 54577 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60571
  rw [data_16_60571.1, data_16_60571.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60571 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60571) < 65536 * m + 60571 := by
  apply descent_of_endpoint
  · rw [data_16_60571.1]; exact data_16_60571.2.2
  · rw [data_16_60571.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 60831). -/
theorem data_16_60831 : oddCount 60831 16 = 10 ∧
    acceleratedOrbit 16 60831 = 54811 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_60831 : ∀ j : Fin 16,
    60831 ≤ acceleratedOrbit j.val 60831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_60831 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60831) = 59049 * m + 54811 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 60831
  rw [data_16_60831.1, data_16_60831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_60831 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 60831) < 65536 * m + 60831 := by
  apply descent_of_endpoint
  · rw [data_16_60831.1]; exact data_16_60831.2.2
  · rw [data_16_60831.2.1]; decide

end Collatz.Research.FirstDescent.Batch094
