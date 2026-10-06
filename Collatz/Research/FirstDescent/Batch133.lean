import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 133. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch133
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 69287). -/
theorem data_18_69287 : oddCount 69287 18 = 11 ∧
    acceleratedOrbit 18 69287 = 46823 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_69287 : ∀ j : Fin 18,
    69287 ≤ acceleratedOrbit j.val 69287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_69287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69287) = 177147 * m + 46823 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 69287
  rw [data_18_69287.1, data_18_69287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_69287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69287) < 262144 * m + 69287 := by
  apply descent_of_endpoint
  · rw [data_18_69287.1]; exact data_18_69287.2.2
  · rw [data_18_69287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 69403). -/
theorem data_18_69403 : oddCount 69403 18 = 11 ∧
    acceleratedOrbit 18 69403 = 46901 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_69403 : ∀ j : Fin 18,
    69403 ≤ acceleratedOrbit j.val 69403 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_69403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69403) = 177147 * m + 46901 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 69403
  rw [data_18_69403.1, data_18_69403.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_69403 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69403) < 262144 * m + 69403 := by
  apply descent_of_endpoint
  · rw [data_18_69403.1]; exact data_18_69403.2.2
  · rw [data_18_69403.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 69407). -/
theorem data_18_69407 : oddCount 69407 18 = 11 ∧
    acceleratedOrbit 18 69407 = 46904 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_69407 : ∀ j : Fin 18,
    69407 ≤ acceleratedOrbit j.val 69407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_69407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69407) = 177147 * m + 46904 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 69407
  rw [data_18_69407.1, data_18_69407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_69407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69407) < 262144 * m + 69407 := by
  apply descent_of_endpoint
  · rw [data_18_69407.1]; exact data_18_69407.2.2
  · rw [data_18_69407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 69487). -/
theorem data_18_69487 : oddCount 69487 18 = 11 ∧
    acceleratedOrbit 18 69487 = 46958 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_69487 : ∀ j : Fin 18,
    69487 ≤ acceleratedOrbit j.val 69487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_69487 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69487) = 177147 * m + 46958 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 69487
  rw [data_18_69487.1, data_18_69487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_69487 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69487) < 262144 * m + 69487 := by
  apply descent_of_endpoint
  · rw [data_18_69487.1]; exact data_18_69487.2.2
  · rw [data_18_69487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 69703). -/
theorem data_18_69703 : oddCount 69703 18 = 11 ∧
    acceleratedOrbit 18 69703 = 47104 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_69703 : ∀ j : Fin 18,
    69703 ≤ acceleratedOrbit j.val 69703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_69703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69703) = 177147 * m + 47104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 69703
  rw [data_18_69703.1, data_18_69703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_69703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69703) < 262144 * m + 69703 := by
  apply descent_of_endpoint
  · rw [data_18_69703.1]; exact data_18_69703.2.2
  · rw [data_18_69703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 69887). -/
theorem data_18_69887 : oddCount 69887 18 = 11 ∧
    acceleratedOrbit 18 69887 = 47228 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_69887 : ∀ j : Fin 18,
    69887 ≤ acceleratedOrbit j.val 69887 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_69887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69887) = 177147 * m + 47228 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 69887
  rw [data_18_69887.1, data_18_69887.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_69887 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69887) < 262144 * m + 69887 := by
  apply descent_of_endpoint
  · rw [data_18_69887.1]; exact data_18_69887.2.2
  · rw [data_18_69887.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 69935). -/
theorem data_18_69935 : oddCount 69935 18 = 11 ∧
    acceleratedOrbit 18 69935 = 47261 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_69935 : ∀ j : Fin 18,
    69935 ≤ acceleratedOrbit j.val 69935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_69935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69935) = 177147 * m + 47261 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 69935
  rw [data_18_69935.1, data_18_69935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_69935 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 69935) < 262144 * m + 69935 := by
  apply descent_of_endpoint
  · rw [data_18_69935.1]; exact data_18_69935.2.2
  · rw [data_18_69935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70047). -/
theorem data_18_70047 : oddCount 70047 18 = 11 ∧
    acceleratedOrbit 18 70047 = 47336 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70047 : ∀ j : Fin 18,
    70047 ≤ acceleratedOrbit j.val 70047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70047) = 177147 * m + 47336 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70047
  rw [data_18_70047.1, data_18_70047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70047) < 262144 * m + 70047 := by
  apply descent_of_endpoint
  · rw [data_18_70047.1]; exact data_18_70047.2.2
  · rw [data_18_70047.2.1]; decide

end Collatz.Research.FirstDescent.Batch133
