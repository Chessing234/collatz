import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 123. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch123
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 51903). -/
theorem data_18_51903 : oddCount 51903 18 = 11 ∧
    acceleratedOrbit 18 51903 = 35075 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_51903 : ∀ j : Fin 18,
    51903 ≤ acceleratedOrbit j.val 51903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_51903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51903) = 177147 * m + 35075 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 51903
  rw [data_18_51903.1, data_18_51903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_51903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51903) < 262144 * m + 51903 := by
  apply descent_of_endpoint
  · rw [data_18_51903.1]; exact data_18_51903.2.2
  · rw [data_18_51903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 51963). -/
theorem data_18_51963 : oddCount 51963 18 = 11 ∧
    acceleratedOrbit 18 51963 = 35116 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_51963 : ∀ j : Fin 18,
    51963 ≤ acceleratedOrbit j.val 51963 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_51963 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51963) = 177147 * m + 35116 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 51963
  rw [data_18_51963.1, data_18_51963.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_51963 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 51963) < 262144 * m + 51963 := by
  apply descent_of_endpoint
  · rw [data_18_51963.1]; exact data_18_51963.2.2
  · rw [data_18_51963.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 52223). -/
theorem data_18_52223 : oddCount 52223 18 = 11 ∧
    acceleratedOrbit 18 52223 = 35291 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_52223 : ∀ j : Fin 18,
    52223 ≤ acceleratedOrbit j.val 52223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_52223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52223) = 177147 * m + 35291 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 52223
  rw [data_18_52223.1, data_18_52223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_52223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52223) < 262144 * m + 52223 := by
  apply descent_of_endpoint
  · rw [data_18_52223.1]; exact data_18_52223.2.2
  · rw [data_18_52223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 52315). -/
theorem data_18_52315 : oddCount 52315 18 = 11 ∧
    acceleratedOrbit 18 52315 = 35354 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_52315 : ∀ j : Fin 18,
    52315 ≤ acceleratedOrbit j.val 52315 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_52315 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52315) = 177147 * m + 35354 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 52315
  rw [data_18_52315.1, data_18_52315.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_52315 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52315) < 262144 * m + 52315 := by
  apply descent_of_endpoint
  · rw [data_18_52315.1]; exact data_18_52315.2.2
  · rw [data_18_52315.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 52475). -/
theorem data_18_52475 : oddCount 52475 18 = 11 ∧
    acceleratedOrbit 18 52475 = 35462 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_52475 : ∀ j : Fin 18,
    52475 ≤ acceleratedOrbit j.val 52475 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_52475 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52475) = 177147 * m + 35462 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 52475
  rw [data_18_52475.1, data_18_52475.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_52475 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52475) < 262144 * m + 52475 := by
  apply descent_of_endpoint
  · rw [data_18_52475.1]; exact data_18_52475.2.2
  · rw [data_18_52475.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 52527). -/
theorem data_18_52527 : oddCount 52527 18 = 11 ∧
    acceleratedOrbit 18 52527 = 35497 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_52527 : ∀ j : Fin 18,
    52527 ≤ acceleratedOrbit j.val 52527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_52527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52527) = 177147 * m + 35497 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 52527
  rw [data_18_52527.1, data_18_52527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_52527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52527) < 262144 * m + 52527 := by
  apply descent_of_endpoint
  · rw [data_18_52527.1]; exact data_18_52527.2.2
  · rw [data_18_52527.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 52767). -/
theorem data_18_52767 : oddCount 52767 18 = 11 ∧
    acceleratedOrbit 18 52767 = 35659 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_52767 : ∀ j : Fin 18,
    52767 ≤ acceleratedOrbit j.val 52767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_52767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52767) = 177147 * m + 35659 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 52767
  rw [data_18_52767.1, data_18_52767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_52767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52767) < 262144 * m + 52767 := by
  apply descent_of_endpoint
  · rw [data_18_52767.1]; exact data_18_52767.2.2
  · rw [data_18_52767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 52927). -/
theorem data_18_52927 : oddCount 52927 18 = 11 ∧
    acceleratedOrbit 18 52927 = 35767 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_52927 : ∀ j : Fin 18,
    52927 ≤ acceleratedOrbit j.val 52927 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_52927 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52927) = 177147 * m + 35767 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 52927
  rw [data_18_52927.1, data_18_52927.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_52927 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 52927) < 262144 * m + 52927 := by
  apply descent_of_endpoint
  · rw [data_18_52927.1]; exact data_18_52927.2.2
  · rw [data_18_52927.2.1]; decide

end Collatz.Research.FirstDescent.Batch123
