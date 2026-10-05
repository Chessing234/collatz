import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 198. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch198
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 213759). -/
theorem data_18_213759 : oddCount 213759 18 = 11 ∧
    acceleratedOrbit 18 213759 = 144451 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_213759 : ∀ j : Fin 18,
    213759 ≤ acceleratedOrbit j.val 213759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_213759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 213759) = 177147 * m + 144451 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 213759
  rw [data_18_213759.1, data_18_213759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_213759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 213759) < 262144 * m + 213759 := by
  apply descent_of_endpoint
  · rw [data_18_213759.1]; exact data_18_213759.2.2
  · rw [data_18_213759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 213851). -/
theorem data_18_213851 : oddCount 213851 18 = 11 ∧
    acceleratedOrbit 18 213851 = 144514 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_213851 : ∀ j : Fin 18,
    213851 ≤ acceleratedOrbit j.val 213851 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_213851 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 213851) = 177147 * m + 144514 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 213851
  rw [data_18_213851.1, data_18_213851.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_213851 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 213851) < 262144 * m + 213851 := by
  apply descent_of_endpoint
  · rw [data_18_213851.1]; exact data_18_213851.2.2
  · rw [data_18_213851.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 214171). -/
theorem data_18_214171 : oddCount 214171 18 = 11 ∧
    acceleratedOrbit 18 214171 = 144730 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_214171 : ∀ j : Fin 18,
    214171 ≤ acceleratedOrbit j.val 214171 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_214171 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214171) = 177147 * m + 144730 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 214171
  rw [data_18_214171.1, data_18_214171.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_214171 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214171) < 262144 * m + 214171 := by
  apply descent_of_endpoint
  · rw [data_18_214171.1]; exact data_18_214171.2.2
  · rw [data_18_214171.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 214271). -/
theorem data_18_214271 : oddCount 214271 18 = 11 ∧
    acceleratedOrbit 18 214271 = 144797 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_214271 : ∀ j : Fin 18,
    214271 ≤ acceleratedOrbit j.val 214271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_214271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214271) = 177147 * m + 144797 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 214271
  rw [data_18_214271.1, data_18_214271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_214271 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214271) < 262144 * m + 214271 := by
  apply descent_of_endpoint
  · rw [data_18_214271.1]; exact data_18_214271.2.2
  · rw [data_18_214271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 214527). -/
theorem data_18_214527 : oddCount 214527 18 = 11 ∧
    acceleratedOrbit 18 214527 = 144970 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_214527 : ∀ j : Fin 18,
    214527 ≤ acceleratedOrbit j.val 214527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_214527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214527) = 177147 * m + 144970 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 214527
  rw [data_18_214527.1, data_18_214527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_214527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214527) < 262144 * m + 214527 := by
  apply descent_of_endpoint
  · rw [data_18_214527.1]; exact data_18_214527.2.2
  · rw [data_18_214527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 214683). -/
theorem data_18_214683 : oddCount 214683 18 = 11 ∧
    acceleratedOrbit 18 214683 = 145076 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_214683 : ∀ j : Fin 18,
    214683 ≤ acceleratedOrbit j.val 214683 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_214683 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214683) = 177147 * m + 145076 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 214683
  rw [data_18_214683.1, data_18_214683.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_214683 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 214683) < 262144 * m + 214683 := by
  apply descent_of_endpoint
  · rw [data_18_214683.1]; exact data_18_214683.2.2
  · rw [data_18_214683.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 215291). -/
theorem data_18_215291 : oddCount 215291 18 = 11 ∧
    acceleratedOrbit 18 215291 = 145487 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_215291 : ∀ j : Fin 18,
    215291 ≤ acceleratedOrbit j.val 215291 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_215291 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215291) = 177147 * m + 145487 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 215291
  rw [data_18_215291.1, data_18_215291.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_215291 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215291) < 262144 * m + 215291 := by
  apply descent_of_endpoint
  · rw [data_18_215291.1]; exact data_18_215291.2.2
  · rw [data_18_215291.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 215367). -/
theorem data_18_215367 : oddCount 215367 18 = 11 ∧
    acceleratedOrbit 18 215367 = 145538 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_215367 : ∀ j : Fin 18,
    215367 ≤ acceleratedOrbit j.val 215367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_215367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215367) = 177147 * m + 145538 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 215367
  rw [data_18_215367.1, data_18_215367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_215367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 215367) < 262144 * m + 215367 := by
  apply descent_of_endpoint
  · rw [data_18_215367.1]; exact data_18_215367.2.2
  · rw [data_18_215367.2.1]; decide

end Collatz.Research.FirstDescent.Batch198
