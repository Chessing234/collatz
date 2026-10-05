import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 60. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch060
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22555). -/
theorem data_16_22555 : oddCount 22555 16 = 10 ∧
    acceleratedOrbit 16 22555 = 20324 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22555 : ∀ j : Fin 16,
    22555 ≤ acceleratedOrbit j.val 22555 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22555 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22555) = 59049 * m + 20324 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22555
  rw [data_16_22555.1, data_16_22555.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22555 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22555) < 65536 * m + 22555 := by
  apply descent_of_endpoint
  · rw [data_16_22555.1]; exact data_16_22555.2.2
  · rw [data_16_22555.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22575). -/
theorem data_16_22575 : oddCount 22575 16 = 10 ∧
    acceleratedOrbit 16 22575 = 20342 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22575 : ∀ j : Fin 16,
    22575 ≤ acceleratedOrbit j.val 22575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22575 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22575) = 59049 * m + 20342 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22575
  rw [data_16_22575.1, data_16_22575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22575 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22575) < 65536 * m + 22575 := by
  apply descent_of_endpoint
  · rw [data_16_22575.1]; exact data_16_22575.2.2
  · rw [data_16_22575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22695). -/
theorem data_16_22695 : oddCount 22695 16 = 10 ∧
    acceleratedOrbit 16 22695 = 20450 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22695 : ∀ j : Fin 16,
    22695 ≤ acceleratedOrbit j.val 22695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22695 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22695) = 59049 * m + 20450 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22695
  rw [data_16_22695.1, data_16_22695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22695 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22695) < 65536 * m + 22695 := by
  apply descent_of_endpoint
  · rw [data_16_22695.1]; exact data_16_22695.2.2
  · rw [data_16_22695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22887). -/
theorem data_16_22887 : oddCount 22887 16 = 10 ∧
    acceleratedOrbit 16 22887 = 20623 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22887 : ∀ j : Fin 16,
    22887 ≤ acceleratedOrbit j.val 22887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22887) = 59049 * m + 20623 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22887
  rw [data_16_22887.1, data_16_22887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22887) < 65536 * m + 22887 := by
  apply descent_of_endpoint
  · rw [data_16_22887.1]; exact data_16_22887.2.2
  · rw [data_16_22887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23143). -/
theorem data_16_23143 : oddCount 23143 16 = 10 ∧
    acceleratedOrbit 16 23143 = 20854 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23143 : ∀ j : Fin 16,
    23143 ≤ acceleratedOrbit j.val 23143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23143) = 59049 * m + 20854 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23143
  rw [data_16_23143.1, data_16_23143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23143 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23143) < 65536 * m + 23143 := by
  apply descent_of_endpoint
  · rw [data_16_23143.1]; exact data_16_23143.2.2
  · rw [data_16_23143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23167). -/
theorem data_16_23167 : oddCount 23167 16 = 10 ∧
    acceleratedOrbit 16 23167 = 20875 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23167 : ∀ j : Fin 16,
    23167 ≤ acceleratedOrbit j.val 23167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23167) = 59049 * m + 20875 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23167
  rw [data_16_23167.1, data_16_23167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23167 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23167) < 65536 * m + 23167 := by
  apply descent_of_endpoint
  · rw [data_16_23167.1]; exact data_16_23167.2.2
  · rw [data_16_23167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23583). -/
theorem data_16_23583 : oddCount 23583 16 = 10 ∧
    acceleratedOrbit 16 23583 = 21250 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23583 : ∀ j : Fin 16,
    23583 ≤ acceleratedOrbit j.val 23583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23583 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23583) = 59049 * m + 21250 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23583
  rw [data_16_23583.1, data_16_23583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23583 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23583) < 65536 * m + 23583 := by
  apply descent_of_endpoint
  · rw [data_16_23583.1]; exact data_16_23583.2.2
  · rw [data_16_23583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 23663). -/
theorem data_16_23663 : oddCount 23663 16 = 10 ∧
    acceleratedOrbit 16 23663 = 21322 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_23663 : ∀ j : Fin 16,
    23663 ≤ acceleratedOrbit j.val 23663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_23663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23663) = 59049 * m + 21322 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 23663
  rw [data_16_23663.1, data_16_23663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_23663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 23663) < 65536 * m + 23663 := by
  apply descent_of_endpoint
  · rw [data_16_23663.1]; exact data_16_23663.2.2
  · rw [data_16_23663.2.1]; decide

end Collatz.Research.FirstDescent.Batch060
