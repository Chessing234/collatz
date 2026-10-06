import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 191. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch191
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 197951). -/
theorem data_18_197951 : oddCount 197951 18 = 11 ∧
    acceleratedOrbit 18 197951 = 133769 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_197951 : ∀ j : Fin 18,
    197951 ≤ acceleratedOrbit j.val 197951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_197951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197951) = 177147 * m + 133769 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 197951
  rw [data_18_197951.1, data_18_197951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_197951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197951) < 262144 * m + 197951 := by
  apply descent_of_endpoint
  · rw [data_18_197951.1]; exact data_18_197951.2.2
  · rw [data_18_197951.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 197991). -/
theorem data_18_197991 : oddCount 197991 18 = 11 ∧
    acceleratedOrbit 18 197991 = 133796 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_197991 : ∀ j : Fin 18,
    197991 ≤ acceleratedOrbit j.val 197991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_197991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197991) = 177147 * m + 133796 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 197991
  rw [data_18_197991.1, data_18_197991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_197991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 197991) < 262144 * m + 197991 := by
  apply descent_of_endpoint
  · rw [data_18_197991.1]; exact data_18_197991.2.2
  · rw [data_18_197991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 198111). -/
theorem data_18_198111 : oddCount 198111 18 = 11 ∧
    acceleratedOrbit 18 198111 = 133877 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_198111 : ∀ j : Fin 18,
    198111 ≤ acceleratedOrbit j.val 198111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_198111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 198111) = 177147 * m + 133877 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 198111
  rw [data_18_198111.1, data_18_198111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_198111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 198111) < 262144 * m + 198111 := by
  apply descent_of_endpoint
  · rw [data_18_198111.1]; exact data_18_198111.2.2
  · rw [data_18_198111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 200127). -/
theorem data_18_200127 : oddCount 200127 18 = 11 ∧
    acceleratedOrbit 18 200127 = 135239 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_200127 : ∀ j : Fin 18,
    200127 ≤ acceleratedOrbit j.val 200127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_200127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 200127) = 177147 * m + 135239 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 200127
  rw [data_18_200127.1, data_18_200127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_200127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 200127) < 262144 * m + 200127 := by
  apply descent_of_endpoint
  · rw [data_18_200127.1]; exact data_18_200127.2.2
  · rw [data_18_200127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 200539). -/
theorem data_18_200539 : oddCount 200539 18 = 11 ∧
    acceleratedOrbit 18 200539 = 135518 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_200539 : ∀ j : Fin 18,
    200539 ≤ acceleratedOrbit j.val 200539 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_200539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 200539) = 177147 * m + 135518 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 200539
  rw [data_18_200539.1, data_18_200539.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_200539 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 200539) < 262144 * m + 200539 := by
  apply descent_of_endpoint
  · rw [data_18_200539.1]; exact data_18_200539.2.2
  · rw [data_18_200539.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 200955). -/
theorem data_18_200955 : oddCount 200955 18 = 11 ∧
    acceleratedOrbit 18 200955 = 135799 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_200955 : ∀ j : Fin 18,
    200955 ≤ acceleratedOrbit j.val 200955 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_200955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 200955) = 177147 * m + 135799 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 200955
  rw [data_18_200955.1, data_18_200955.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_200955 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 200955) < 262144 * m + 200955 := by
  apply descent_of_endpoint
  · rw [data_18_200955.1]; exact data_18_200955.2.2
  · rw [data_18_200955.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 201307). -/
theorem data_18_201307 : oddCount 201307 18 = 11 ∧
    acceleratedOrbit 18 201307 = 136037 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_201307 : ∀ j : Fin 18,
    201307 ≤ acceleratedOrbit j.val 201307 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_201307 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 201307) = 177147 * m + 136037 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 201307
  rw [data_18_201307.1, data_18_201307.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_201307 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 201307) < 262144 * m + 201307 := by
  apply descent_of_endpoint
  · rw [data_18_201307.1]; exact data_18_201307.2.2
  · rw [data_18_201307.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 201663). -/
theorem data_18_201663 : oddCount 201663 18 = 11 ∧
    acceleratedOrbit 18 201663 = 136277 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_201663 : ∀ j : Fin 18,
    201663 ≤ acceleratedOrbit j.val 201663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_201663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 201663) = 177147 * m + 136277 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 201663
  rw [data_18_201663.1, data_18_201663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_201663 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 201663) < 262144 * m + 201663 := by
  apply descent_of_endpoint
  · rw [data_18_201663.1]; exact data_18_201663.2.2
  · rw [data_18_201663.2.1]; decide

end Collatz.Research.FirstDescent.Batch191
