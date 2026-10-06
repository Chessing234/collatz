import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 35. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch035
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 24303). -/
theorem data_15_24303 : oddCount 24303 15 = 9 ∧
    acceleratedOrbit 15 24303 = 14599 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_24303 : ∀ j : Fin 15,
    24303 ≤ acceleratedOrbit j.val 24303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_24303 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24303) = 19683 * m + 14599 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 24303
  rw [data_15_24303.1, data_15_24303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_24303 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24303) < 32768 * m + 24303 := by
  apply descent_of_endpoint
  · rw [data_15_24303.1]; exact data_15_24303.2.2
  · rw [data_15_24303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 24559). -/
theorem data_15_24559 : oddCount 24559 15 = 9 ∧
    acceleratedOrbit 15 24559 = 14753 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_24559 : ∀ j : Fin 15,
    24559 ≤ acceleratedOrbit j.val 24559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_24559 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24559) = 19683 * m + 14753 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 24559
  rw [data_15_24559.1, data_15_24559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_24559 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24559) < 32768 * m + 24559 := by
  apply descent_of_endpoint
  · rw [data_15_24559.1]; exact data_15_24559.2.2
  · rw [data_15_24559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 24639). -/
theorem data_15_24639 : oddCount 24639 15 = 9 ∧
    acceleratedOrbit 15 24639 = 14801 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_24639 : ∀ j : Fin 15,
    24639 ≤ acceleratedOrbit j.val 24639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_24639 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24639) = 19683 * m + 14801 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 24639
  rw [data_15_24639.1, data_15_24639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_24639 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24639) < 32768 * m + 24639 := by
  apply descent_of_endpoint
  · rw [data_15_24639.1]; exact data_15_24639.2.2
  · rw [data_15_24639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 24647). -/
theorem data_15_24647 : oddCount 24647 15 = 9 ∧
    acceleratedOrbit 15 24647 = 14806 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_24647 : ∀ j : Fin 15,
    24647 ≤ acceleratedOrbit j.val 24647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_24647 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24647) = 19683 * m + 14806 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 24647
  rw [data_15_24647.1, data_15_24647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_24647 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24647) < 32768 * m + 24647 := by
  apply descent_of_endpoint
  · rw [data_15_24647.1]; exact data_15_24647.2.2
  · rw [data_15_24647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 24679). -/
theorem data_15_24679 : oddCount 24679 15 = 9 ∧
    acceleratedOrbit 15 24679 = 14825 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_24679 : ∀ j : Fin 15,
    24679 ≤ acceleratedOrbit j.val 24679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_24679 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24679) = 19683 * m + 14825 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 24679
  rw [data_15_24679.1, data_15_24679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_24679 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 24679) < 32768 * m + 24679 := by
  apply descent_of_endpoint
  · rw [data_15_24679.1]; exact data_15_24679.2.2
  · rw [data_15_24679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 25247). -/
theorem data_15_25247 : oddCount 25247 15 = 9 ∧
    acceleratedOrbit 15 25247 = 15166 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_25247 : ∀ j : Fin 15,
    25247 ≤ acceleratedOrbit j.val 25247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_25247 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25247) = 19683 * m + 15166 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 25247
  rw [data_15_25247.1, data_15_25247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_25247 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25247) < 32768 * m + 25247 := by
  apply descent_of_endpoint
  · rw [data_15_25247.1]; exact data_15_25247.2.2
  · rw [data_15_25247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 25503). -/
theorem data_15_25503 : oddCount 25503 15 = 9 ∧
    acceleratedOrbit 15 25503 = 15320 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_25503 : ∀ j : Fin 15,
    25503 ≤ acceleratedOrbit j.val 25503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_25503 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25503) = 19683 * m + 15320 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 25503
  rw [data_15_25503.1, data_15_25503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_25503 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25503) < 32768 * m + 25503 := by
  apply descent_of_endpoint
  · rw [data_15_25503.1]; exact data_15_25503.2.2
  · rw [data_15_25503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (15, 25583). -/
theorem data_15_25583 : oddCount 25583 15 = 9 ∧
    acceleratedOrbit 15 25583 = 15368 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_25583 : ∀ j : Fin 15,
    25583 ≤ acceleratedOrbit j.val 25583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_25583 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25583) = 19683 * m + 15368 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 25583
  rw [data_15_25583.1, data_15_25583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_25583 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 25583) < 32768 * m + 25583 := by
  apply descent_of_endpoint
  · rw [data_15_25583.1]; exact data_15_25583.2.2
  · rw [data_15_25583.2.1]; decide

end Collatz.Research.FirstDescent.Batch035
