import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 59. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch059
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 21595). -/
theorem data_16_21595 : oddCount 21595 16 = 10 ∧
    acceleratedOrbit 16 21595 = 19459 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_21595 : ∀ j : Fin 16,
    21595 ≤ acceleratedOrbit j.val 21595 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_21595 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21595) = 59049 * m + 19459 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 21595
  rw [data_16_21595.1, data_16_21595.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_21595 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21595) < 65536 * m + 21595 := by
  apply descent_of_endpoint
  · rw [data_16_21595.1]; exact data_16_21595.2.2
  · rw [data_16_21595.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 21615). -/
theorem data_16_21615 : oddCount 21615 16 = 10 ∧
    acceleratedOrbit 16 21615 = 19477 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_21615 : ∀ j : Fin 16,
    21615 ≤ acceleratedOrbit j.val 21615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_21615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21615) = 59049 * m + 19477 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 21615
  rw [data_16_21615.1, data_16_21615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_21615 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21615) < 65536 * m + 21615 := by
  apply descent_of_endpoint
  · rw [data_16_21615.1]; exact data_16_21615.2.2
  · rw [data_16_21615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 21695). -/
theorem data_16_21695 : oddCount 21695 16 = 10 ∧
    acceleratedOrbit 16 21695 = 19549 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_21695 : ∀ j : Fin 16,
    21695 ≤ acceleratedOrbit j.val 21695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_21695 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21695) = 59049 * m + 19549 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 21695
  rw [data_16_21695.1, data_16_21695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_21695 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21695) < 65536 * m + 21695 := by
  apply descent_of_endpoint
  · rw [data_16_21695.1]; exact data_16_21695.2.2
  · rw [data_16_21695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 21735). -/
theorem data_16_21735 : oddCount 21735 16 = 10 ∧
    acceleratedOrbit 16 21735 = 19585 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_21735 : ∀ j : Fin 16,
    21735 ≤ acceleratedOrbit j.val 21735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_21735 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21735) = 59049 * m + 19585 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 21735
  rw [data_16_21735.1, data_16_21735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_21735 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 21735) < 65536 * m + 21735 := by
  apply descent_of_endpoint
  · rw [data_16_21735.1]; exact data_16_21735.2.2
  · rw [data_16_21735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22015). -/
theorem data_16_22015 : oddCount 22015 16 = 10 ∧
    acceleratedOrbit 16 22015 = 19837 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22015 : ∀ j : Fin 16,
    22015 ≤ acceleratedOrbit j.val 22015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22015) = 59049 * m + 19837 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22015
  rw [data_16_22015.1, data_16_22015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22015) < 65536 * m + 22015 := by
  apply descent_of_endpoint
  · rw [data_16_22015.1]; exact data_16_22015.2.2
  · rw [data_16_22015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22119). -/
theorem data_16_22119 : oddCount 22119 16 = 10 ∧
    acceleratedOrbit 16 22119 = 19931 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22119 : ∀ j : Fin 16,
    22119 ≤ acceleratedOrbit j.val 22119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22119) = 59049 * m + 19931 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22119
  rw [data_16_22119.1, data_16_22119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22119 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22119) < 65536 * m + 22119 := by
  apply descent_of_endpoint
  · rw [data_16_22119.1]; exact data_16_22119.2.2
  · rw [data_16_22119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22399). -/
theorem data_16_22399 : oddCount 22399 16 = 10 ∧
    acceleratedOrbit 16 22399 = 20183 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22399 : ∀ j : Fin 16,
    22399 ≤ acceleratedOrbit j.val 22399 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22399 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22399) = 59049 * m + 20183 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22399
  rw [data_16_22399.1, data_16_22399.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22399 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22399) < 65536 * m + 22399 := by
  apply descent_of_endpoint
  · rw [data_16_22399.1]; exact data_16_22399.2.2
  · rw [data_16_22399.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 22495). -/
theorem data_16_22495 : oddCount 22495 16 = 10 ∧
    acceleratedOrbit 16 22495 = 20270 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_22495 : ∀ j : Fin 16,
    22495 ≤ acceleratedOrbit j.val 22495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_22495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22495) = 59049 * m + 20270 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 22495
  rw [data_16_22495.1, data_16_22495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_22495 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 22495) < 65536 * m + 22495 := by
  apply descent_of_endpoint
  · rw [data_16_22495.1]; exact data_16_22495.2.2
  · rw [data_16_22495.2.1]; decide

end Collatz.Research.FirstDescent.Batch059
