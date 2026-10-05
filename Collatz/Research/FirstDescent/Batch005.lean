import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 5. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch005
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1087). -/
theorem data_12_1087 : oddCount 1087 12 = 7 ∧
    acceleratedOrbit 12 1087 = 581 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1087 : ∀ j : Fin 12,
    1087 ≤ acceleratedOrbit j.val 1087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1087 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1087) = 2187 * m + 581 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1087
  rw [data_12_1087.1, data_12_1087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1087 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1087) < 4096 * m + 1087 := by
  apply descent_of_endpoint
  · rw [data_12_1087.1]; exact data_12_1087.2.2
  · rw [data_12_1087.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1231). -/
theorem data_12_1231 : oddCount 1231 12 = 7 ∧
    acceleratedOrbit 12 1231 = 658 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1231 : ∀ j : Fin 12,
    1231 ≤ acceleratedOrbit j.val 1231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1231 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1231) = 2187 * m + 658 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1231
  rw [data_12_1231.1, data_12_1231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1231 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1231) < 4096 * m + 1231 := by
  apply descent_of_endpoint
  · rw [data_12_1231.1]; exact data_12_1231.2.2
  · rw [data_12_1231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1435). -/
theorem data_12_1435 : oddCount 1435 12 = 7 ∧
    acceleratedOrbit 12 1435 = 767 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1435 : ∀ j : Fin 12,
    1435 ≤ acceleratedOrbit j.val 1435 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1435 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1435) = 2187 * m + 767 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1435
  rw [data_12_1435.1, data_12_1435.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1435 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1435) < 4096 * m + 1435 := by
  apply descent_of_endpoint
  · rw [data_12_1435.1]; exact data_12_1435.2.2
  · rw [data_12_1435.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1647). -/
theorem data_12_1647 : oddCount 1647 12 = 7 ∧
    acceleratedOrbit 12 1647 = 880 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1647 : ∀ j : Fin 12,
    1647 ≤ acceleratedOrbit j.val 1647 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1647 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1647) = 2187 * m + 880 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1647
  rw [data_12_1647.1, data_12_1647.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1647 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1647) < 4096 * m + 1647 := by
  apply descent_of_endpoint
  · rw [data_12_1647.1]; exact data_12_1647.2.2
  · rw [data_12_1647.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1703). -/
theorem data_12_1703 : oddCount 1703 12 = 7 ∧
    acceleratedOrbit 12 1703 = 910 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1703 : ∀ j : Fin 12,
    1703 ≤ acceleratedOrbit j.val 1703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1703 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1703) = 2187 * m + 910 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1703
  rw [data_12_1703.1, data_12_1703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1703 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1703) < 4096 * m + 1703 := by
  apply descent_of_endpoint
  · rw [data_12_1703.1]; exact data_12_1703.2.2
  · rw [data_12_1703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1787). -/
theorem data_12_1787 : oddCount 1787 12 = 7 ∧
    acceleratedOrbit 12 1787 = 955 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1787 : ∀ j : Fin 12,
    1787 ≤ acceleratedOrbit j.val 1787 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1787 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1787) = 2187 * m + 955 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1787
  rw [data_12_1787.1, data_12_1787.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1787 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1787) < 4096 * m + 1787 := by
  apply descent_of_endpoint
  · rw [data_12_1787.1]; exact data_12_1787.2.2
  · rw [data_12_1787.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1823). -/
theorem data_12_1823 : oddCount 1823 12 = 7 ∧
    acceleratedOrbit 12 1823 = 974 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1823 : ∀ j : Fin 12,
    1823 ≤ acceleratedOrbit j.val 1823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1823 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1823) = 2187 * m + 974 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1823
  rw [data_12_1823.1, data_12_1823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1823 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1823) < 4096 * m + 1823 := by
  apply descent_of_endpoint
  · rw [data_12_1823.1]; exact data_12_1823.2.2
  · rw [data_12_1823.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 1855). -/
theorem data_12_1855 : oddCount 1855 12 = 7 ∧
    acceleratedOrbit 12 1855 = 991 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_1855 : ∀ j : Fin 12,
    1855 ≤ acceleratedOrbit j.val 1855 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_1855 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1855) = 2187 * m + 991 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 1855
  rw [data_12_1855.1, data_12_1855.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_1855 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 1855) < 4096 * m + 1855 := by
  apply descent_of_endpoint
  · rw [data_12_1855.1]; exact data_12_1855.2.2
  · rw [data_12_1855.2.1]; decide

end Collatz.Research.FirstDescent.Batch005
