import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 155. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch155
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 114843). -/
theorem data_18_114843 : oddCount 114843 18 = 11 ∧
    acceleratedOrbit 18 114843 = 77608 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_114843 : ∀ j : Fin 18,
    114843 ≤ acceleratedOrbit j.val 114843 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_114843 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 114843) = 177147 * m + 77608 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 114843
  rw [data_18_114843.1, data_18_114843.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_114843 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 114843) < 262144 * m + 114843 := by
  apply descent_of_endpoint
  · rw [data_18_114843.1]; exact data_18_114843.2.2
  · rw [data_18_114843.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 115431). -/
theorem data_18_115431 : oddCount 115431 18 = 11 ∧
    acceleratedOrbit 18 115431 = 78005 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_115431 : ∀ j : Fin 18,
    115431 ≤ acceleratedOrbit j.val 115431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_115431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 115431) = 177147 * m + 78005 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 115431
  rw [data_18_115431.1, data_18_115431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_115431 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 115431) < 262144 * m + 115431 := by
  apply descent_of_endpoint
  · rw [data_18_115431.1]; exact data_18_115431.2.2
  · rw [data_18_115431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 115963). -/
theorem data_18_115963 : oddCount 115963 18 = 11 ∧
    acceleratedOrbit 18 115963 = 78365 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_115963 : ∀ j : Fin 18,
    115963 ≤ acceleratedOrbit j.val 115963 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_115963 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 115963) = 177147 * m + 78365 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 115963
  rw [data_18_115963.1, data_18_115963.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_115963 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 115963) < 262144 * m + 115963 := by
  apply descent_of_endpoint
  · rw [data_18_115963.1]; exact data_18_115963.2.2
  · rw [data_18_115963.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 116175). -/
theorem data_18_116175 : oddCount 116175 18 = 11 ∧
    acceleratedOrbit 18 116175 = 78508 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_116175 : ∀ j : Fin 18,
    116175 ≤ acceleratedOrbit j.val 116175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_116175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 116175) = 177147 * m + 78508 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 116175
  rw [data_18_116175.1, data_18_116175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_116175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 116175) < 262144 * m + 116175 := by
  apply descent_of_endpoint
  · rw [data_18_116175.1]; exact data_18_116175.2.2
  · rw [data_18_116175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 116455). -/
theorem data_18_116455 : oddCount 116455 18 = 11 ∧
    acceleratedOrbit 18 116455 = 78697 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_116455 : ∀ j : Fin 18,
    116455 ≤ acceleratedOrbit j.val 116455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_116455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 116455) = 177147 * m + 78697 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 116455
  rw [data_18_116455.1, data_18_116455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_116455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 116455) < 262144 * m + 116455 := by
  apply descent_of_endpoint
  · rw [data_18_116455.1]; exact data_18_116455.2.2
  · rw [data_18_116455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 116647). -/
theorem data_18_116647 : oddCount 116647 18 = 11 ∧
    acceleratedOrbit 18 116647 = 78827 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_116647 : ∀ j : Fin 18,
    116647 ≤ acceleratedOrbit j.val 116647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_116647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 116647) = 177147 * m + 78827 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 116647
  rw [data_18_116647.1, data_18_116647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_116647 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 116647) < 262144 * m + 116647 := by
  apply descent_of_endpoint
  · rw [data_18_116647.1]; exact data_18_116647.2.2
  · rw [data_18_116647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 117415). -/
theorem data_18_117415 : oddCount 117415 18 = 11 ∧
    acceleratedOrbit 18 117415 = 79346 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_117415 : ∀ j : Fin 18,
    117415 ≤ acceleratedOrbit j.val 117415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_117415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117415) = 177147 * m + 79346 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 117415
  rw [data_18_117415.1, data_18_117415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_117415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117415) < 262144 * m + 117415 := by
  apply descent_of_endpoint
  · rw [data_18_117415.1]; exact data_18_117415.2.2
  · rw [data_18_117415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 117455). -/
theorem data_18_117455 : oddCount 117455 18 = 11 ∧
    acceleratedOrbit 18 117455 = 79373 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_117455 : ∀ j : Fin 18,
    117455 ≤ acceleratedOrbit j.val 117455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_117455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117455) = 177147 * m + 79373 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 117455
  rw [data_18_117455.1, data_18_117455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_117455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 117455) < 262144 * m + 117455 := by
  apply descent_of_endpoint
  · rw [data_18_117455.1]; exact data_18_117455.2.2
  · rw [data_18_117455.2.1]; decide

end Collatz.Research.FirstDescent.Batch155
