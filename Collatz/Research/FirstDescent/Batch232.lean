import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 232. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch232
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 32047). -/
theorem data_20_32047 : oddCount 32047 20 = 12 ∧
    acceleratedOrbit 20 32047 = 16243 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_32047 : ∀ j : Fin 20,
    32047 ≤ acceleratedOrbit j.val 32047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_32047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32047) = 531441 * m + 16243 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 32047
  rw [data_20_32047.1, data_20_32047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_32047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32047) < 1048576 * m + 32047 := by
  apply descent_of_endpoint
  · rw [data_20_32047.1]; exact data_20_32047.2.2
  · rw [data_20_32047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 32639). -/
theorem data_20_32639 : oddCount 32639 20 = 12 ∧
    acceleratedOrbit 20 32639 = 16543 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_32639 : ∀ j : Fin 20,
    32639 ≤ acceleratedOrbit j.val 32639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_32639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32639) = 531441 * m + 16543 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 32639
  rw [data_20_32639.1, data_20_32639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_32639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32639) < 1048576 * m + 32639 := by
  apply descent_of_endpoint
  · rw [data_20_32639.1]; exact data_20_32639.2.2
  · rw [data_20_32639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 32799). -/
theorem data_20_32799 : oddCount 32799 20 = 12 ∧
    acceleratedOrbit 20 32799 = 16624 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_32799 : ∀ j : Fin 20,
    32799 ≤ acceleratedOrbit j.val 32799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_32799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32799) = 531441 * m + 16624 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 32799
  rw [data_20_32799.1, data_20_32799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_32799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32799) < 1048576 * m + 32799 := by
  apply descent_of_endpoint
  · rw [data_20_32799.1]; exact data_20_32799.2.2
  · rw [data_20_32799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 32935). -/
theorem data_20_32935 : oddCount 32935 20 = 12 ∧
    acceleratedOrbit 20 32935 = 16693 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_32935 : ∀ j : Fin 20,
    32935 ≤ acceleratedOrbit j.val 32935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_32935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32935) = 531441 * m + 16693 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 32935
  rw [data_20_32935.1, data_20_32935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_32935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 32935) < 1048576 * m + 32935 := by
  apply descent_of_endpoint
  · rw [data_20_32935.1]; exact data_20_32935.2.2
  · rw [data_20_32935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 33511). -/
theorem data_20_33511 : oddCount 33511 20 = 12 ∧
    acceleratedOrbit 20 33511 = 16985 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_33511 : ∀ j : Fin 20,
    33511 ≤ acceleratedOrbit j.val 33511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_33511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 33511) = 531441 * m + 16985 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 33511
  rw [data_20_33511.1, data_20_33511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_33511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 33511) < 1048576 * m + 33511 := by
  apply descent_of_endpoint
  · rw [data_20_33511.1]; exact data_20_33511.2.2
  · rw [data_20_33511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 33535). -/
theorem data_20_33535 : oddCount 33535 20 = 12 ∧
    acceleratedOrbit 20 33535 = 16997 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_33535 : ∀ j : Fin 20,
    33535 ≤ acceleratedOrbit j.val 33535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_33535 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 33535) = 531441 * m + 16997 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 33535
  rw [data_20_33535.1, data_20_33535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_33535 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 33535) < 1048576 * m + 33535 := by
  apply descent_of_endpoint
  · rw [data_20_33535.1]; exact data_20_33535.2.2
  · rw [data_20_33535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 33819). -/
theorem data_20_33819 : oddCount 33819 20 = 12 ∧
    acceleratedOrbit 20 33819 = 17141 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_33819 : ∀ j : Fin 20,
    33819 ≤ acceleratedOrbit j.val 33819 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_33819 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 33819) = 531441 * m + 17141 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 33819
  rw [data_20_33819.1, data_20_33819.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_33819 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 33819) < 1048576 * m + 33819 := by
  apply descent_of_endpoint
  · rw [data_20_33819.1]; exact data_20_33819.2.2
  · rw [data_20_33819.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 34983). -/
theorem data_20_34983 : oddCount 34983 20 = 12 ∧
    acceleratedOrbit 20 34983 = 17731 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_34983 : ∀ j : Fin 20,
    34983 ≤ acceleratedOrbit j.val 34983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_34983 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 34983) = 531441 * m + 17731 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 34983
  rw [data_20_34983.1, data_20_34983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_34983 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 34983) < 1048576 * m + 34983 := by
  apply descent_of_endpoint
  · rw [data_20_34983.1]; exact data_20_34983.2.2
  · rw [data_20_34983.2.1]; decide

end Collatz.Research.FirstDescent.Batch232
