import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 137. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch137
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 77007). -/
theorem data_18_77007 : oddCount 77007 18 = 11 ∧
    acceleratedOrbit 18 77007 = 52040 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_77007 : ∀ j : Fin 18,
    77007 ≤ acceleratedOrbit j.val 77007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_77007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77007) = 177147 * m + 52040 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 77007
  rw [data_18_77007.1, data_18_77007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_77007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77007) < 262144 * m + 77007 := by
  apply descent_of_endpoint
  · rw [data_18_77007.1]; exact data_18_77007.2.2
  · rw [data_18_77007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 77119). -/
theorem data_18_77119 : oddCount 77119 18 = 11 ∧
    acceleratedOrbit 18 77119 = 52115 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_77119 : ∀ j : Fin 18,
    77119 ≤ acceleratedOrbit j.val 77119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_77119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77119) = 177147 * m + 52115 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 77119
  rw [data_18_77119.1, data_18_77119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_77119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77119) < 262144 * m + 77119 := by
  apply descent_of_endpoint
  · rw [data_18_77119.1]; exact data_18_77119.2.2
  · rw [data_18_77119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 77127). -/
theorem data_18_77127 : oddCount 77127 18 = 11 ∧
    acceleratedOrbit 18 77127 = 52121 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_77127 : ∀ j : Fin 18,
    77127 ≤ acceleratedOrbit j.val 77127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_77127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77127) = 177147 * m + 52121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 77127
  rw [data_18_77127.1, data_18_77127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_77127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77127) < 262144 * m + 77127 := by
  apply descent_of_endpoint
  · rw [data_18_77127.1]; exact data_18_77127.2.2
  · rw [data_18_77127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 77295). -/
theorem data_18_77295 : oddCount 77295 18 = 11 ∧
    acceleratedOrbit 18 77295 = 52234 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_77295 : ∀ j : Fin 18,
    77295 ≤ acceleratedOrbit j.val 77295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_77295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77295) = 177147 * m + 52234 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 77295
  rw [data_18_77295.1, data_18_77295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_77295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77295) < 262144 * m + 77295 := by
  apply descent_of_endpoint
  · rw [data_18_77295.1]; exact data_18_77295.2.2
  · rw [data_18_77295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 77339). -/
theorem data_18_77339 : oddCount 77339 18 = 11 ∧
    acceleratedOrbit 18 77339 = 52264 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_77339 : ∀ j : Fin 18,
    77339 ≤ acceleratedOrbit j.val 77339 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_77339 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77339) = 177147 * m + 52264 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 77339
  rw [data_18_77339.1, data_18_77339.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_77339 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77339) < 262144 * m + 77339 := by
  apply descent_of_endpoint
  · rw [data_18_77339.1]; exact data_18_77339.2.2
  · rw [data_18_77339.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 77727). -/
theorem data_18_77727 : oddCount 77727 18 = 11 ∧
    acceleratedOrbit 18 77727 = 52526 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_77727 : ∀ j : Fin 18,
    77727 ≤ acceleratedOrbit j.val 77727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_77727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77727) = 177147 * m + 52526 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 77727
  rw [data_18_77727.1, data_18_77727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_77727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77727) < 262144 * m + 77727 := by
  apply descent_of_endpoint
  · rw [data_18_77727.1]; exact data_18_77727.2.2
  · rw [data_18_77727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 77851). -/
theorem data_18_77851 : oddCount 77851 18 = 11 ∧
    acceleratedOrbit 18 77851 = 52610 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_77851 : ∀ j : Fin 18,
    77851 ≤ acceleratedOrbit j.val 77851 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_77851 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77851) = 177147 * m + 52610 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 77851
  rw [data_18_77851.1, data_18_77851.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_77851 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 77851) < 262144 * m + 77851 := by
  apply descent_of_endpoint
  · rw [data_18_77851.1]; exact data_18_77851.2.2
  · rw [data_18_77851.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 78619). -/
theorem data_18_78619 : oddCount 78619 18 = 11 ∧
    acceleratedOrbit 18 78619 = 53129 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_78619 : ∀ j : Fin 18,
    78619 ≤ acceleratedOrbit j.val 78619 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_78619 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 78619) = 177147 * m + 53129 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 78619
  rw [data_18_78619.1, data_18_78619.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_78619 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 78619) < 262144 * m + 78619 := by
  apply descent_of_endpoint
  · rw [data_18_78619.1]; exact data_18_78619.2.2
  · rw [data_18_78619.2.1]; decide

end Collatz.Research.FirstDescent.Batch137
