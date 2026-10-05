import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 38. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch038
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 29467). -/
theorem data_15_29467 : oddCount 29467 15 = 9 ∧
    acceleratedOrbit 15 29467 = 17701 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_29467 : ∀ j : Fin 15,
    29467 ≤ acceleratedOrbit j.val 29467 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_29467 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 29467) = 19683 * m + 17701 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 29467
  rw [data_15_29467.1, data_15_29467.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_29467 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 29467) < 32768 * m + 29467 := by
  apply descent_of_endpoint
  · rw [data_15_29467.1]; exact data_15_29467.2.2
  · rw [data_15_29467.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 29743). -/
theorem data_15_29743 : oddCount 29743 15 = 9 ∧
    acceleratedOrbit 15 29743 = 17867 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_29743 : ∀ j : Fin 15,
    29743 ≤ acceleratedOrbit j.val 29743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_29743 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 29743) = 19683 * m + 17867 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 29743
  rw [data_15_29743.1, data_15_29743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_29743 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 29743) < 32768 * m + 29743 := by
  apply descent_of_endpoint
  · rw [data_15_29743.1]; exact data_15_29743.2.2
  · rw [data_15_29743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 29863). -/
theorem data_15_29863 : oddCount 29863 15 = 9 ∧
    acceleratedOrbit 15 29863 = 17939 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_29863 : ∀ j : Fin 15,
    29863 ≤ acceleratedOrbit j.val 29863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_29863 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 29863) = 19683 * m + 17939 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 29863
  rw [data_15_29863.1, data_15_29863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_29863 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 29863) < 32768 * m + 29863 := by
  apply descent_of_endpoint
  · rw [data_15_29863.1]; exact data_15_29863.2.2
  · rw [data_15_29863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 30311). -/
theorem data_15_30311 : oddCount 30311 15 = 9 ∧
    acceleratedOrbit 15 30311 = 18208 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_30311 : ∀ j : Fin 15,
    30311 ≤ acceleratedOrbit j.val 30311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_30311 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30311) = 19683 * m + 18208 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 30311
  rw [data_15_30311.1, data_15_30311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_30311 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30311) < 32768 * m + 30311 := by
  apply descent_of_endpoint
  · rw [data_15_30311.1]; exact data_15_30311.2.2
  · rw [data_15_30311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 30591). -/
theorem data_15_30591 : oddCount 30591 15 = 9 ∧
    acceleratedOrbit 15 30591 = 18376 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_30591 : ∀ j : Fin 15,
    30591 ≤ acceleratedOrbit j.val 30591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_30591 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30591) = 19683 * m + 18376 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 30591
  rw [data_15_30591.1, data_15_30591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_30591 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30591) < 32768 * m + 30591 := by
  apply descent_of_endpoint
  · rw [data_15_30591.1]; exact data_15_30591.2.2
  · rw [data_15_30591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 30687). -/
theorem data_15_30687 : oddCount 30687 15 = 9 ∧
    acceleratedOrbit 15 30687 = 18434 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_30687 : ∀ j : Fin 15,
    30687 ≤ acceleratedOrbit j.val 30687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_30687 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30687) = 19683 * m + 18434 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 30687
  rw [data_15_30687.1, data_15_30687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_30687 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30687) < 32768 * m + 30687 := by
  apply descent_of_endpoint
  · rw [data_15_30687.1]; exact data_15_30687.2.2
  · rw [data_15_30687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 30715). -/
theorem data_15_30715 : oddCount 30715 15 = 9 ∧
    acceleratedOrbit 15 30715 = 18451 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_30715 : ∀ j : Fin 15,
    30715 ≤ acceleratedOrbit j.val 30715 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_30715 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30715) = 19683 * m + 18451 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 30715
  rw [data_15_30715.1, data_15_30715.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_30715 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30715) < 32768 * m + 30715 := by
  apply descent_of_endpoint
  · rw [data_15_30715.1]; exact data_15_30715.2.2
  · rw [data_15_30715.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 30747). -/
theorem data_15_30747 : oddCount 30747 15 = 9 ∧
    acceleratedOrbit 15 30747 = 18470 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_30747 : ∀ j : Fin 15,
    30747 ≤ acceleratedOrbit j.val 30747 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_30747 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30747) = 19683 * m + 18470 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 30747
  rw [data_15_30747.1, data_15_30747.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_30747 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 30747) < 32768 * m + 30747 := by
  apply descent_of_endpoint
  · rw [data_15_30747.1]; exact data_15_30747.2.2
  · rw [data_15_30747.2.1]; decide

end Collatz.Research.FirstDescent.Batch038
