import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 106. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch106
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 12911). -/
theorem data_18_12911 : oddCount 12911 18 = 11 ∧
    acceleratedOrbit 18 12911 = 8726 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_12911 : ∀ j : Fin 18,
    12911 ≤ acceleratedOrbit j.val 12911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_12911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12911) = 177147 * m + 8726 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 12911
  rw [data_18_12911.1, data_18_12911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_12911 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 12911) < 262144 * m + 12911 := by
  apply descent_of_endpoint
  · rw [data_18_12911.1]; exact data_18_12911.2.2
  · rw [data_18_12911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13031). -/
theorem data_18_13031 : oddCount 13031 18 = 11 ∧
    acceleratedOrbit 18 13031 = 8807 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13031 : ∀ j : Fin 18,
    13031 ≤ acceleratedOrbit j.val 13031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13031) = 177147 * m + 8807 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13031
  rw [data_18_13031.1, data_18_13031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13031) < 262144 * m + 13031 := by
  apply descent_of_endpoint
  · rw [data_18_13031.1]; exact data_18_13031.2.2
  · rw [data_18_13031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13127). -/
theorem data_18_13127 : oddCount 13127 18 = 11 ∧
    acceleratedOrbit 18 13127 = 8872 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13127 : ∀ j : Fin 18,
    13127 ≤ acceleratedOrbit j.val 13127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13127) = 177147 * m + 8872 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13127
  rw [data_18_13127.1, data_18_13127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13127) < 262144 * m + 13127 := by
  apply descent_of_endpoint
  · rw [data_18_13127.1]; exact data_18_13127.2.2
  · rw [data_18_13127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13359). -/
theorem data_18_13359 : oddCount 13359 18 = 11 ∧
    acceleratedOrbit 18 13359 = 9029 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13359 : ∀ j : Fin 18,
    13359 ≤ acceleratedOrbit j.val 13359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13359) = 177147 * m + 9029 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13359
  rw [data_18_13359.1, data_18_13359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13359 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13359) < 262144 * m + 13359 := by
  apply descent_of_endpoint
  · rw [data_18_13359.1]; exact data_18_13359.2.2
  · rw [data_18_13359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13471). -/
theorem data_18_13471 : oddCount 13471 18 = 11 ∧
    acceleratedOrbit 18 13471 = 9104 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13471 : ∀ j : Fin 18,
    13471 ≤ acceleratedOrbit j.val 13471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13471) = 177147 * m + 9104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13471
  rw [data_18_13471.1, data_18_13471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13471) < 262144 * m + 13471 := by
  apply descent_of_endpoint
  · rw [data_18_13471.1]; exact data_18_13471.2.2
  · rw [data_18_13471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13479). -/
theorem data_18_13479 : oddCount 13479 18 = 11 ∧
    acceleratedOrbit 18 13479 = 9110 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13479 : ∀ j : Fin 18,
    13479 ≤ acceleratedOrbit j.val 13479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13479) = 177147 * m + 9110 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13479
  rw [data_18_13479.1, data_18_13479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13479 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13479) < 262144 * m + 13479 := by
  apply descent_of_endpoint
  · rw [data_18_13479.1]; exact data_18_13479.2.2
  · rw [data_18_13479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13595). -/
theorem data_18_13595 : oddCount 13595 18 = 11 ∧
    acceleratedOrbit 18 13595 = 9188 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13595 : ∀ j : Fin 18,
    13595 ≤ acceleratedOrbit j.val 13595 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13595 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13595) = 177147 * m + 9188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13595
  rw [data_18_13595.1, data_18_13595.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13595 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13595) < 262144 * m + 13595 := by
  apply descent_of_endpoint
  · rw [data_18_13595.1]; exact data_18_13595.2.2
  · rw [data_18_13595.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 13639). -/
theorem data_18_13639 : oddCount 13639 18 = 11 ∧
    acceleratedOrbit 18 13639 = 9218 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_13639 : ∀ j : Fin 18,
    13639 ≤ acceleratedOrbit j.val 13639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_13639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13639) = 177147 * m + 9218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 13639
  rw [data_18_13639.1, data_18_13639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_13639 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 13639) < 262144 * m + 13639 := by
  apply descent_of_endpoint
  · rw [data_18_13639.1]; exact data_18_13639.2.2
  · rw [data_18_13639.2.1]; decide

end Collatz.Research.FirstDescent.Batch106
