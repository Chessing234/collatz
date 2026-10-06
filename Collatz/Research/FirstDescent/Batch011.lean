import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 11. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch011
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2331). -/
theorem data_13_2331 : oddCount 2331 13 = 8 ∧
    acceleratedOrbit 13 2331 = 1868 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2331 : ∀ j : Fin 13,
    2331 ≤ acceleratedOrbit j.val 2331 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2331 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2331) = 6561 * m + 1868 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2331
  rw [data_13_2331.1, data_13_2331.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2331 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2331) < 8192 * m + 2331 := by
  apply descent_of_endpoint
  · rw [data_13_2331.1]; exact data_13_2331.2.2
  · rw [data_13_2331.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2431). -/
theorem data_13_2431 : oddCount 2431 13 = 8 ∧
    acceleratedOrbit 13 2431 = 1948 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2431 : ∀ j : Fin 13,
    2431 ≤ acceleratedOrbit j.val 2431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2431 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2431) = 6561 * m + 1948 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2431
  rw [data_13_2431.1, data_13_2431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2431 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2431) < 8192 * m + 2431 := by
  apply descent_of_endpoint
  · rw [data_13_2431.1]; exact data_13_2431.2.2
  · rw [data_13_2431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2607). -/
theorem data_13_2607 : oddCount 2607 13 = 8 ∧
    acceleratedOrbit 13 2607 = 2089 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2607 : ∀ j : Fin 13,
    2607 ≤ acceleratedOrbit j.val 2607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2607 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2607) = 6561 * m + 2089 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2607
  rw [data_13_2607.1, data_13_2607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2607 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2607) < 8192 * m + 2607 := by
  apply descent_of_endpoint
  · rw [data_13_2607.1]; exact data_13_2607.2.2
  · rw [data_13_2607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 2663). -/
theorem data_13_2663 : oddCount 2663 13 = 8 ∧
    acceleratedOrbit 13 2663 = 2134 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_2663 : ∀ j : Fin 13,
    2663 ≤ acceleratedOrbit j.val 2663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_2663 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2663) = 6561 * m + 2134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 2663
  rw [data_13_2663.1, data_13_2663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_2663 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 2663) < 8192 * m + 2663 := by
  apply descent_of_endpoint
  · rw [data_13_2663.1]; exact data_13_2663.2.2
  · rw [data_13_2663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3039). -/
theorem data_13_3039 : oddCount 3039 13 = 8 ∧
    acceleratedOrbit 13 3039 = 2435 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3039 : ∀ j : Fin 13,
    3039 ≤ acceleratedOrbit j.val 3039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3039 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3039) = 6561 * m + 2435 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3039
  rw [data_13_3039.1, data_13_3039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3039 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3039) < 8192 * m + 3039 := by
  apply descent_of_endpoint
  · rw [data_13_3039.1]; exact data_13_3039.2.2
  · rw [data_13_3039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3067). -/
theorem data_13_3067 : oddCount 3067 13 = 8 ∧
    acceleratedOrbit 13 3067 = 2458 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3067 : ∀ j : Fin 13,
    3067 ≤ acceleratedOrbit j.val 3067 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3067 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3067) = 6561 * m + 2458 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3067
  rw [data_13_3067.1, data_13_3067.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3067 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3067) < 8192 * m + 3067 := by
  apply descent_of_endpoint
  · rw [data_13_3067.1]; exact data_13_3067.2.2
  · rw [data_13_3067.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3135). -/
theorem data_13_3135 : oddCount 3135 13 = 8 ∧
    acceleratedOrbit 13 3135 = 2512 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3135 : ∀ j : Fin 13,
    3135 ≤ acceleratedOrbit j.val 3135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3135 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3135) = 6561 * m + 2512 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3135
  rw [data_13_3135.1, data_13_3135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3135 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3135) < 8192 * m + 3135 := by
  apply descent_of_endpoint
  · rw [data_13_3135.1]; exact data_13_3135.2.2
  · rw [data_13_3135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (13, 3455). -/
theorem data_13_3455 : oddCount 3455 13 = 8 ∧
    acceleratedOrbit 13 3455 = 2768 ∧ 6561 < 8192 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_13_3455 : ∀ j : Fin 13,
    3455 ≤ acceleratedOrbit j.val 3455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_13_3455 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3455) = 6561 * m + 2768 := by
  have h := Congruence.accOrbit_pow_two_mul_add 13 m 3455
  rw [data_13_3455.1, data_13_3455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_13_3455 (m : Nat) :
    acceleratedOrbit 13 (8192 * m + 3455) < 8192 * m + 3455 := by
  apply descent_of_endpoint
  · rw [data_13_3455.1]; exact data_13_3455.2.2
  · rw [data_13_3455.2.1]; decide

end Collatz.Research.FirstDescent.Batch011
