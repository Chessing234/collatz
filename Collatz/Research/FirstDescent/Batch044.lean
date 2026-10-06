import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 44. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch044
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4799). -/
theorem data_16_4799 : oddCount 4799 16 = 10 ∧
    acceleratedOrbit 16 4799 = 4325 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4799 : ∀ j : Fin 16,
    4799 ≤ acceleratedOrbit j.val 4799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4799 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4799) = 59049 * m + 4325 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4799
  rw [data_16_4799.1, data_16_4799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4799 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4799) < 65536 * m + 4799 := by
  apply descent_of_endpoint
  · rw [data_16_4799.1]; exact data_16_4799.2.2
  · rw [data_16_4799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4815). -/
theorem data_16_4815 : oddCount 4815 16 = 10 ∧
    acceleratedOrbit 16 4815 = 4340 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4815 : ∀ j : Fin 16,
    4815 ≤ acceleratedOrbit j.val 4815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4815 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4815) = 59049 * m + 4340 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4815
  rw [data_16_4815.1, data_16_4815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4815 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4815) < 65536 * m + 4815 := by
  apply descent_of_endpoint
  · rw [data_16_4815.1]; exact data_16_4815.2.2
  · rw [data_16_4815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4895). -/
theorem data_16_4895 : oddCount 4895 16 = 10 ∧
    acceleratedOrbit 16 4895 = 4412 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4895 : ∀ j : Fin 16,
    4895 ≤ acceleratedOrbit j.val 4895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4895 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4895) = 59049 * m + 4412 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4895
  rw [data_16_4895.1, data_16_4895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4895 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4895) < 65536 * m + 4895 := by
  apply descent_of_endpoint
  · rw [data_16_4895.1]; exact data_16_4895.2.2
  · rw [data_16_4895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 4991). -/
theorem data_16_4991 : oddCount 4991 16 = 10 ∧
    acceleratedOrbit 16 4991 = 4498 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_4991 : ∀ j : Fin 16,
    4991 ≤ acceleratedOrbit j.val 4991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_4991 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4991) = 59049 * m + 4498 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 4991
  rw [data_16_4991.1, data_16_4991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_4991 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 4991) < 65536 * m + 4991 := by
  apply descent_of_endpoint
  · rw [data_16_4991.1]; exact data_16_4991.2.2
  · rw [data_16_4991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5087). -/
theorem data_16_5087 : oddCount 5087 16 = 10 ∧
    acceleratedOrbit 16 5087 = 4585 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5087 : ∀ j : Fin 16,
    5087 ≤ acceleratedOrbit j.val 5087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5087 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5087) = 59049 * m + 4585 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5087
  rw [data_16_5087.1, data_16_5087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5087 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5087) < 65536 * m + 5087 := by
  apply descent_of_endpoint
  · rw [data_16_5087.1]; exact data_16_5087.2.2
  · rw [data_16_5087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5343). -/
theorem data_16_5343 : oddCount 5343 16 = 10 ∧
    acceleratedOrbit 16 5343 = 4816 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5343 : ∀ j : Fin 16,
    5343 ≤ acceleratedOrbit j.val 5343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5343) = 59049 * m + 4816 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5343
  rw [data_16_5343.1, data_16_5343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5343) < 65536 * m + 5343 := by
  apply descent_of_endpoint
  · rw [data_16_5343.1]; exact data_16_5343.2.2
  · rw [data_16_5343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5375). -/
theorem data_16_5375 : oddCount 5375 16 = 10 ∧
    acceleratedOrbit 16 5375 = 4844 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5375 : ∀ j : Fin 16,
    5375 ≤ acceleratedOrbit j.val 5375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5375) = 59049 * m + 4844 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5375
  rw [data_16_5375.1, data_16_5375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5375 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5375) < 65536 * m + 5375 := by
  apply descent_of_endpoint
  · rw [data_16_5375.1]; exact data_16_5375.2.2
  · rw [data_16_5375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5423). -/
theorem data_16_5423 : oddCount 5423 16 = 10 ∧
    acceleratedOrbit 16 5423 = 4888 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5423 : ∀ j : Fin 16,
    5423 ≤ acceleratedOrbit j.val 5423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5423) = 59049 * m + 4888 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5423
  rw [data_16_5423.1, data_16_5423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5423 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5423) < 65536 * m + 5423 := by
  apply descent_of_endpoint
  · rw [data_16_5423.1]; exact data_16_5423.2.2
  · rw [data_16_5423.2.1]; decide

end Collatz.Research.FirstDescent.Batch044
