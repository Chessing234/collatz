import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 248. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch248
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 77915). -/
theorem data_20_77915 : oddCount 77915 20 = 12 ∧
    acceleratedOrbit 20 77915 = 39490 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_77915 : ∀ j : Fin 20,
    77915 ≤ acceleratedOrbit j.val 77915 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_77915 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 77915) = 531441 * m + 39490 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 77915
  rw [data_20_77915.1, data_20_77915.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_77915 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 77915) < 1048576 * m + 77915 := by
  apply descent_of_endpoint
  · rw [data_20_77915.1]; exact data_20_77915.2.2
  · rw [data_20_77915.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 78847). -/
theorem data_20_78847 : oddCount 78847 20 = 12 ∧
    acceleratedOrbit 20 78847 = 39962 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_78847 : ∀ j : Fin 20,
    78847 ≤ acceleratedOrbit j.val 78847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_78847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 78847) = 531441 * m + 39962 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 78847
  rw [data_20_78847.1, data_20_78847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_78847 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 78847) < 1048576 * m + 78847 := by
  apply descent_of_endpoint
  · rw [data_20_78847.1]; exact data_20_78847.2.2
  · rw [data_20_78847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 78959). -/
theorem data_20_78959 : oddCount 78959 20 = 12 ∧
    acceleratedOrbit 20 78959 = 40019 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_78959 : ∀ j : Fin 20,
    78959 ≤ acceleratedOrbit j.val 78959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_78959 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 78959) = 531441 * m + 40019 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 78959
  rw [data_20_78959.1, data_20_78959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_78959 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 78959) < 1048576 * m + 78959 := by
  apply descent_of_endpoint
  · rw [data_20_78959.1]; exact data_20_78959.2.2
  · rw [data_20_78959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 79407). -/
theorem data_20_79407 : oddCount 79407 20 = 12 ∧
    acceleratedOrbit 20 79407 = 40246 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_79407 : ∀ j : Fin 20,
    79407 ≤ acceleratedOrbit j.val 79407 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_79407 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 79407) = 531441 * m + 40246 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 79407
  rw [data_20_79407.1, data_20_79407.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_79407 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 79407) < 1048576 * m + 79407 := by
  apply descent_of_endpoint
  · rw [data_20_79407.1]; exact data_20_79407.2.2
  · rw [data_20_79407.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 79983). -/
theorem data_20_79983 : oddCount 79983 20 = 12 ∧
    acceleratedOrbit 20 79983 = 40538 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_79983 : ∀ j : Fin 20,
    79983 ≤ acceleratedOrbit j.val 79983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_79983 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 79983) = 531441 * m + 40538 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 79983
  rw [data_20_79983.1, data_20_79983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_79983 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 79983) < 1048576 * m + 79983 := by
  apply descent_of_endpoint
  · rw [data_20_79983.1]; exact data_20_79983.2.2
  · rw [data_20_79983.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 79999). -/
theorem data_20_79999 : oddCount 79999 20 = 12 ∧
    acceleratedOrbit 20 79999 = 40546 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_79999 : ∀ j : Fin 20,
    79999 ≤ acceleratedOrbit j.val 79999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_79999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 79999) = 531441 * m + 40546 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 79999
  rw [data_20_79999.1, data_20_79999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_79999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 79999) < 1048576 * m + 79999 := by
  apply descent_of_endpoint
  · rw [data_20_79999.1]; exact data_20_79999.2.2
  · rw [data_20_79999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 80095). -/
theorem data_20_80095 : oddCount 80095 20 = 12 ∧
    acceleratedOrbit 20 80095 = 40595 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_80095 : ∀ j : Fin 20,
    80095 ≤ acceleratedOrbit j.val 80095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_80095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80095) = 531441 * m + 40595 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 80095
  rw [data_20_80095.1, data_20_80095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_80095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80095) < 1048576 * m + 80095 := by
  apply descent_of_endpoint
  · rw [data_20_80095.1]; exact data_20_80095.2.2
  · rw [data_20_80095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 80255). -/
theorem data_20_80255 : oddCount 80255 20 = 12 ∧
    acceleratedOrbit 20 80255 = 40676 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_80255 : ∀ j : Fin 20,
    80255 ≤ acceleratedOrbit j.val 80255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_80255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80255) = 531441 * m + 40676 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 80255
  rw [data_20_80255.1, data_20_80255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_80255 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 80255) < 1048576 * m + 80255 := by
  apply descent_of_endpoint
  · rw [data_20_80255.1]; exact data_20_80255.2.2
  · rw [data_20_80255.2.1]; decide

end Collatz.Research.FirstDescent.Batch248
