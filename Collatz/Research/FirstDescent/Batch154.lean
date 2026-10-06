import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 154. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch154
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112687). -/
theorem data_18_112687 : oddCount 112687 18 = 11 ∧
    acceleratedOrbit 18 112687 = 76151 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112687 : ∀ j : Fin 18,
    112687 ≤ acceleratedOrbit j.val 112687 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112687) = 177147 * m + 76151 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112687
  rw [data_18_112687.1, data_18_112687.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112687 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112687) < 262144 * m + 112687 := by
  apply descent_of_endpoint
  · rw [data_18_112687.1]; exact data_18_112687.2.2
  · rw [data_18_112687.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112807). -/
theorem data_18_112807 : oddCount 112807 18 = 11 ∧
    acceleratedOrbit 18 112807 = 76232 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112807 : ∀ j : Fin 18,
    112807 ≤ acceleratedOrbit j.val 112807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112807) = 177147 * m + 76232 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112807
  rw [data_18_112807.1, data_18_112807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112807) < 262144 * m + 112807 := by
  apply descent_of_endpoint
  · rw [data_18_112807.1]; exact data_18_112807.2.2
  · rw [data_18_112807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112847). -/
theorem data_18_112847 : oddCount 112847 18 = 11 ∧
    acceleratedOrbit 18 112847 = 76259 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112847 : ∀ j : Fin 18,
    112847 ≤ acceleratedOrbit j.val 112847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112847) = 177147 * m + 76259 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112847
  rw [data_18_112847.1, data_18_112847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112847) < 262144 * m + 112847 := by
  apply descent_of_endpoint
  · rw [data_18_112847.1]; exact data_18_112847.2.2
  · rw [data_18_112847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 112895). -/
theorem data_18_112895 : oddCount 112895 18 = 11 ∧
    acceleratedOrbit 18 112895 = 76291 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_112895 : ∀ j : Fin 18,
    112895 ≤ acceleratedOrbit j.val 112895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_112895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112895) = 177147 * m + 76291 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 112895
  rw [data_18_112895.1, data_18_112895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_112895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 112895) < 262144 * m + 112895 := by
  apply descent_of_endpoint
  · rw [data_18_112895.1]; exact data_18_112895.2.2
  · rw [data_18_112895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 113051). -/
theorem data_18_113051 : oddCount 113051 18 = 11 ∧
    acceleratedOrbit 18 113051 = 76397 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_113051 : ∀ j : Fin 18,
    113051 ≤ acceleratedOrbit j.val 113051 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_113051 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 113051) = 177147 * m + 76397 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 113051
  rw [data_18_113051.1, data_18_113051.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_113051 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 113051) < 262144 * m + 113051 := by
  apply descent_of_endpoint
  · rw [data_18_113051.1]; exact data_18_113051.2.2
  · rw [data_18_113051.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 113407). -/
theorem data_18_113407 : oddCount 113407 18 = 11 ∧
    acceleratedOrbit 18 113407 = 76637 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_113407 : ∀ j : Fin 18,
    113407 ≤ acceleratedOrbit j.val 113407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_113407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 113407) = 177147 * m + 76637 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 113407
  rw [data_18_113407.1, data_18_113407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_113407 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 113407) < 262144 * m + 113407 := by
  apply descent_of_endpoint
  · rw [data_18_113407.1]; exact data_18_113407.2.2
  · rw [data_18_113407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 113819). -/
theorem data_18_113819 : oddCount 113819 18 = 11 ∧
    acceleratedOrbit 18 113819 = 76916 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_113819 : ∀ j : Fin 18,
    113819 ≤ acceleratedOrbit j.val 113819 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_113819 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 113819) = 177147 * m + 76916 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 113819
  rw [data_18_113819.1, data_18_113819.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_113819 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 113819) < 262144 * m + 113819 := by
  apply descent_of_endpoint
  · rw [data_18_113819.1]; exact data_18_113819.2.2
  · rw [data_18_113819.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 114683). -/
theorem data_18_114683 : oddCount 114683 18 = 11 ∧
    acceleratedOrbit 18 114683 = 77500 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_114683 : ∀ j : Fin 18,
    114683 ≤ acceleratedOrbit j.val 114683 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_114683 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 114683) = 177147 * m + 77500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 114683
  rw [data_18_114683.1, data_18_114683.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_114683 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 114683) < 262144 * m + 114683 := by
  apply descent_of_endpoint
  · rw [data_18_114683.1]; exact data_18_114683.2.2
  · rw [data_18_114683.2.1]; decide

end Collatz.Research.FirstDescent.Batch154
