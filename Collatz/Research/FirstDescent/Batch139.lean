import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 139. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch139
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 81647). -/
theorem data_18_81647 : oddCount 81647 18 = 11 ∧
    acceleratedOrbit 18 81647 = 55175 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_81647 : ∀ j : Fin 18,
    81647 ≤ acceleratedOrbit j.val 81647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_81647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 81647) = 177147 * m + 55175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 81647
  rw [data_18_81647.1, data_18_81647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_81647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 81647) < 262144 * m + 81647 := by
  apply descent_of_endpoint
  · rw [data_18_81647.1]; exact data_18_81647.2.2
  · rw [data_18_81647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 82335). -/
theorem data_18_82335 : oddCount 82335 18 = 11 ∧
    acceleratedOrbit 18 82335 = 55640 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_82335 : ∀ j : Fin 18,
    82335 ≤ acceleratedOrbit j.val 82335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_82335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 82335) = 177147 * m + 55640 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 82335
  rw [data_18_82335.1, data_18_82335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_82335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 82335) < 262144 * m + 82335 := by
  apply descent_of_endpoint
  · rw [data_18_82335.1]; exact data_18_82335.2.2
  · rw [data_18_82335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 83431). -/
theorem data_18_83431 : oddCount 83431 18 = 11 ∧
    acceleratedOrbit 18 83431 = 56381 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_83431 : ∀ j : Fin 18,
    83431 ≤ acceleratedOrbit j.val 83431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_83431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 83431) = 177147 * m + 56381 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 83431
  rw [data_18_83431.1, data_18_83431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_83431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 83431) < 262144 * m + 83431 := by
  apply descent_of_endpoint
  · rw [data_18_83431.1]; exact data_18_83431.2.2
  · rw [data_18_83431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 83439). -/
theorem data_18_83439 : oddCount 83439 18 = 11 ∧
    acceleratedOrbit 18 83439 = 56386 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_83439 : ∀ j : Fin 18,
    83439 ≤ acceleratedOrbit j.val 83439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_83439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 83439) = 177147 * m + 56386 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 83439
  rw [data_18_83439.1, data_18_83439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_83439 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 83439) < 262144 * m + 83439 := by
  apply descent_of_endpoint
  · rw [data_18_83439.1]; exact data_18_83439.2.2
  · rw [data_18_83439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 83871). -/
theorem data_18_83871 : oddCount 83871 18 = 11 ∧
    acceleratedOrbit 18 83871 = 56678 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_83871 : ∀ j : Fin 18,
    83871 ≤ acceleratedOrbit j.val 83871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_83871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 83871) = 177147 * m + 56678 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 83871
  rw [data_18_83871.1, data_18_83871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_83871 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 83871) < 262144 * m + 83871 := by
  apply descent_of_endpoint
  · rw [data_18_83871.1]; exact data_18_83871.2.2
  · rw [data_18_83871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84031). -/
theorem data_18_84031 : oddCount 84031 18 = 11 ∧
    acceleratedOrbit 18 84031 = 56786 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84031 : ∀ j : Fin 18,
    84031 ≤ acceleratedOrbit j.val 84031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84031) = 177147 * m + 56786 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84031
  rw [data_18_84031.1, data_18_84031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84031) < 262144 * m + 84031 := by
  apply descent_of_endpoint
  · rw [data_18_84031.1]; exact data_18_84031.2.2
  · rw [data_18_84031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84039). -/
theorem data_18_84039 : oddCount 84039 18 = 11 ∧
    acceleratedOrbit 18 84039 = 56792 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84039 : ∀ j : Fin 18,
    84039 ≤ acceleratedOrbit j.val 84039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84039) = 177147 * m + 56792 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84039
  rw [data_18_84039.1, data_18_84039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84039) < 262144 * m + 84039 := by
  apply descent_of_endpoint
  · rw [data_18_84039.1]; exact data_18_84039.2.2
  · rw [data_18_84039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 84071). -/
theorem data_18_84071 : oddCount 84071 18 = 11 ∧
    acceleratedOrbit 18 84071 = 56813 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_84071 : ∀ j : Fin 18,
    84071 ≤ acceleratedOrbit j.val 84071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_84071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84071) = 177147 * m + 56813 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 84071
  rw [data_18_84071.1, data_18_84071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_84071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 84071) < 262144 * m + 84071 := by
  apply descent_of_endpoint
  · rw [data_18_84071.1]; exact data_18_84071.2.2
  · rw [data_18_84071.2.1]; decide

end Collatz.Research.FirstDescent.Batch139
