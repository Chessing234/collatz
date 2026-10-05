import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 42. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch042
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2671). -/
theorem data_16_2671 : oddCount 2671 16 = 10 ∧
    acceleratedOrbit 16 2671 = 2408 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2671 : ∀ j : Fin 16,
    2671 ≤ acceleratedOrbit j.val 2671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2671) = 59049 * m + 2408 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2671
  rw [data_16_2671.1, data_16_2671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2671 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2671) < 65536 * m + 2671 := by
  apply descent_of_endpoint
  · rw [data_16_2671.1]; exact data_16_2671.2.2
  · rw [data_16_2671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2687). -/
theorem data_16_2687 : oddCount 2687 16 = 10 ∧
    acceleratedOrbit 16 2687 = 2422 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2687 : ∀ j : Fin 16,
    2687 ≤ acceleratedOrbit j.val 2687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2687) = 59049 * m + 2422 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2687
  rw [data_16_2687.1, data_16_2687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2687 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2687) < 65536 * m + 2687 := by
  apply descent_of_endpoint
  · rw [data_16_2687.1]; exact data_16_2687.2.2
  · rw [data_16_2687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2791). -/
theorem data_16_2791 : oddCount 2791 16 = 10 ∧
    acceleratedOrbit 16 2791 = 2516 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2791 : ∀ j : Fin 16,
    2791 ≤ acceleratedOrbit j.val 2791 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2791 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2791) = 59049 * m + 2516 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2791
  rw [data_16_2791.1, data_16_2791.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2791 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2791) < 65536 * m + 2791 := by
  apply descent_of_endpoint
  · rw [data_16_2791.1]; exact data_16_2791.2.2
  · rw [data_16_2791.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2887). -/
theorem data_16_2887 : oddCount 2887 16 = 10 ∧
    acceleratedOrbit 16 2887 = 2603 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2887 : ∀ j : Fin 16,
    2887 ≤ acceleratedOrbit j.val 2887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2887) = 59049 * m + 2603 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2887
  rw [data_16_2887.1, data_16_2887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2887 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2887) < 65536 * m + 2887 := by
  apply descent_of_endpoint
  · rw [data_16_2887.1]; exact data_16_2887.2.2
  · rw [data_16_2887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 2927). -/
theorem data_16_2927 : oddCount 2927 16 = 10 ∧
    acceleratedOrbit 16 2927 = 2639 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_2927 : ∀ j : Fin 16,
    2927 ≤ acceleratedOrbit j.val 2927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_2927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2927) = 59049 * m + 2639 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 2927
  rw [data_16_2927.1, data_16_2927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_2927 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 2927) < 65536 * m + 2927 := by
  apply descent_of_endpoint
  · rw [data_16_2927.1]; exact data_16_2927.2.2
  · rw [data_16_2927.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 3103). -/
theorem data_16_3103 : oddCount 3103 16 = 10 ∧
    acceleratedOrbit 16 3103 = 2797 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_3103 : ∀ j : Fin 16,
    3103 ≤ acceleratedOrbit j.val 3103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_3103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3103) = 59049 * m + 2797 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 3103
  rw [data_16_3103.1, data_16_3103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_3103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3103) < 65536 * m + 3103 := by
  apply descent_of_endpoint
  · rw [data_16_3103.1]; exact data_16_3103.2.2
  · rw [data_16_3103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 3239). -/
theorem data_16_3239 : oddCount 3239 16 = 10 ∧
    acceleratedOrbit 16 3239 = 2920 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_3239 : ∀ j : Fin 16,
    3239 ≤ acceleratedOrbit j.val 3239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_3239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3239) = 59049 * m + 2920 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 3239
  rw [data_16_3239.1, data_16_3239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_3239 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3239) < 65536 * m + 3239 := by
  apply descent_of_endpoint
  · rw [data_16_3239.1]; exact data_16_3239.2.2
  · rw [data_16_3239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 3487). -/
theorem data_16_3487 : oddCount 3487 16 = 10 ∧
    acceleratedOrbit 16 3487 = 3143 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_3487 : ∀ j : Fin 16,
    3487 ≤ acceleratedOrbit j.val 3487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_3487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3487) = 59049 * m + 3143 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 3487
  rw [data_16_3487.1, data_16_3487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_3487 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 3487) < 65536 * m + 3487 := by
  apply descent_of_endpoint
  · rw [data_16_3487.1]; exact data_16_3487.2.2
  · rw [data_16_3487.2.1]; decide

end Collatz.Research.FirstDescent.Batch042
