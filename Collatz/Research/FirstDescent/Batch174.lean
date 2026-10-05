import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 174. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch174
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 159967). -/
theorem data_18_159967 : oddCount 159967 18 = 11 ∧
    acceleratedOrbit 18 159967 = 108101 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_159967 : ∀ j : Fin 18,
    159967 ≤ acceleratedOrbit j.val 159967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_159967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159967) = 177147 * m + 108101 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 159967
  rw [data_18_159967.1, data_18_159967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_159967 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 159967) < 262144 * m + 159967 := by
  apply descent_of_endpoint
  · rw [data_18_159967.1]; exact data_18_159967.2.2
  · rw [data_18_159967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 160255). -/
theorem data_18_160255 : oddCount 160255 18 = 11 ∧
    acceleratedOrbit 18 160255 = 108295 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_160255 : ∀ j : Fin 18,
    160255 ≤ acceleratedOrbit j.val 160255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_160255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 160255) = 177147 * m + 108295 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 160255
  rw [data_18_160255.1, data_18_160255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_160255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 160255) < 262144 * m + 160255 := by
  apply descent_of_endpoint
  · rw [data_18_160255.1]; exact data_18_160255.2.2
  · rw [data_18_160255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 160991). -/
theorem data_18_160991 : oddCount 160991 18 = 11 ∧
    acceleratedOrbit 18 160991 = 108793 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_160991 : ∀ j : Fin 18,
    160991 ≤ acceleratedOrbit j.val 160991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_160991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 160991) = 177147 * m + 108793 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 160991
  rw [data_18_160991.1, data_18_160991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_160991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 160991) < 262144 * m + 160991 := by
  apply descent_of_endpoint
  · rw [data_18_160991.1]; exact data_18_160991.2.2
  · rw [data_18_160991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 161071). -/
theorem data_18_161071 : oddCount 161071 18 = 11 ∧
    acceleratedOrbit 18 161071 = 108847 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_161071 : ∀ j : Fin 18,
    161071 ≤ acceleratedOrbit j.val 161071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_161071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161071) = 177147 * m + 108847 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 161071
  rw [data_18_161071.1, data_18_161071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_161071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161071) < 262144 * m + 161071 := by
  apply descent_of_endpoint
  · rw [data_18_161071.1]; exact data_18_161071.2.2
  · rw [data_18_161071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 161311). -/
theorem data_18_161311 : oddCount 161311 18 = 11 ∧
    acceleratedOrbit 18 161311 = 109009 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_161311 : ∀ j : Fin 18,
    161311 ≤ acceleratedOrbit j.val 161311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_161311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161311) = 177147 * m + 109009 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 161311
  rw [data_18_161311.1, data_18_161311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_161311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161311) < 262144 * m + 161311 := by
  apply descent_of_endpoint
  · rw [data_18_161311.1]; exact data_18_161311.2.2
  · rw [data_18_161311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 161471). -/
theorem data_18_161471 : oddCount 161471 18 = 11 ∧
    acceleratedOrbit 18 161471 = 109117 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_161471 : ∀ j : Fin 18,
    161471 ≤ acceleratedOrbit j.val 161471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_161471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161471) = 177147 * m + 109117 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 161471
  rw [data_18_161471.1, data_18_161471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_161471 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161471) < 262144 * m + 161471 := by
  apply descent_of_endpoint
  · rw [data_18_161471.1]; exact data_18_161471.2.2
  · rw [data_18_161471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 161703). -/
theorem data_18_161703 : oddCount 161703 18 = 11 ∧
    acceleratedOrbit 18 161703 = 109274 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_161703 : ∀ j : Fin 18,
    161703 ≤ acceleratedOrbit j.val 161703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_161703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161703) = 177147 * m + 109274 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 161703
  rw [data_18_161703.1, data_18_161703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_161703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161703) < 262144 * m + 161703 := by
  apply descent_of_endpoint
  · rw [data_18_161703.1]; exact data_18_161703.2.2
  · rw [data_18_161703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 161823). -/
theorem data_18_161823 : oddCount 161823 18 = 11 ∧
    acceleratedOrbit 18 161823 = 109355 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_161823 : ∀ j : Fin 18,
    161823 ≤ acceleratedOrbit j.val 161823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_161823 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161823) = 177147 * m + 109355 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 161823
  rw [data_18_161823.1, data_18_161823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_161823 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 161823) < 262144 * m + 161823 := by
  apply descent_of_endpoint
  · rw [data_18_161823.1]; exact data_18_161823.2.2
  · rw [data_18_161823.2.1]; decide

end Collatz.Research.FirstDescent.Batch174
