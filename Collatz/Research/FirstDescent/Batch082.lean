import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 82. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch082
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 45851). -/
theorem data_16_45851 : oddCount 45851 16 = 10 ∧
    acceleratedOrbit 16 45851 = 41314 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_45851 : ∀ j : Fin 16,
    45851 ≤ acceleratedOrbit j.val 45851 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_45851 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45851) = 59049 * m + 41314 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 45851
  rw [data_16_45851.1, data_16_45851.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_45851 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 45851) < 65536 * m + 45851 := by
  apply descent_of_endpoint
  · rw [data_16_45851.1]; exact data_16_45851.2.2
  · rw [data_16_45851.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 46127). -/
theorem data_16_46127 : oddCount 46127 16 = 10 ∧
    acceleratedOrbit 16 46127 = 41563 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_46127 : ∀ j : Fin 16,
    46127 ≤ acceleratedOrbit j.val 46127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_46127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 46127) = 59049 * m + 41563 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 46127
  rw [data_16_46127.1, data_16_46127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_46127 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 46127) < 65536 * m + 46127 := by
  apply descent_of_endpoint
  · rw [data_16_46127.1]; exact data_16_46127.2.2
  · rw [data_16_46127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 46247). -/
theorem data_16_46247 : oddCount 46247 16 = 10 ∧
    acceleratedOrbit 16 46247 = 41671 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_46247 : ∀ j : Fin 16,
    46247 ≤ acceleratedOrbit j.val 46247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_46247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 46247) = 59049 * m + 41671 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 46247
  rw [data_16_46247.1, data_16_46247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_46247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 46247) < 65536 * m + 46247 := by
  apply descent_of_endpoint
  · rw [data_16_46247.1]; exact data_16_46247.2.2
  · rw [data_16_46247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 46407). -/
theorem data_16_46407 : oddCount 46407 16 = 10 ∧
    acceleratedOrbit 16 46407 = 41815 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_46407 : ∀ j : Fin 16,
    46407 ≤ acceleratedOrbit j.val 46407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_46407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 46407) = 59049 * m + 41815 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 46407
  rw [data_16_46407.1, data_16_46407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_46407 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 46407) < 65536 * m + 46407 := by
  apply descent_of_endpoint
  · rw [data_16_46407.1]; exact data_16_46407.2.2
  · rw [data_16_46407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 47099). -/
theorem data_16_47099 : oddCount 47099 16 = 10 ∧
    acceleratedOrbit 16 47099 = 42439 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_47099 : ∀ j : Fin 16,
    47099 ≤ acceleratedOrbit j.val 47099 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_47099 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47099) = 59049 * m + 42439 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 47099
  rw [data_16_47099.1, data_16_47099.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_47099 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47099) < 65536 * m + 47099 := by
  apply descent_of_endpoint
  · rw [data_16_47099.1]; exact data_16_47099.2.2
  · rw [data_16_47099.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 47231). -/
theorem data_16_47231 : oddCount 47231 16 = 10 ∧
    acceleratedOrbit 16 47231 = 42557 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_47231 : ∀ j : Fin 16,
    47231 ≤ acceleratedOrbit j.val 47231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_47231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47231) = 59049 * m + 42557 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 47231
  rw [data_16_47231.1, data_16_47231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_47231 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47231) < 65536 * m + 47231 := by
  apply descent_of_endpoint
  · rw [data_16_47231.1]; exact data_16_47231.2.2
  · rw [data_16_47231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 47327). -/
theorem data_16_47327 : oddCount 47327 16 = 10 ∧
    acceleratedOrbit 16 47327 = 42644 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_47327 : ∀ j : Fin 16,
    47327 ≤ acceleratedOrbit j.val 47327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_47327 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47327) = 59049 * m + 42644 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 47327
  rw [data_16_47327.1, data_16_47327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_47327 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47327) < 65536 * m + 47327 := by
  apply descent_of_endpoint
  · rw [data_16_47327.1]; exact data_16_47327.2.2
  · rw [data_16_47327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 47387). -/
theorem data_16_47387 : oddCount 47387 16 = 10 ∧
    acceleratedOrbit 16 47387 = 42698 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_47387 : ∀ j : Fin 16,
    47387 ≤ acceleratedOrbit j.val 47387 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_47387 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47387) = 59049 * m + 42698 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 47387
  rw [data_16_47387.1, data_16_47387.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_47387 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 47387) < 65536 * m + 47387 := by
  apply descent_of_endpoint
  · rw [data_16_47387.1]; exact data_16_47387.2.2
  · rw [data_16_47387.2.1]; decide

end Collatz.Research.FirstDescent.Batch082
