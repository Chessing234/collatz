import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 194. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch194
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 205467). -/
theorem data_18_205467 : oddCount 205467 18 = 11 ∧
    acceleratedOrbit 18 205467 = 138848 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_205467 : ∀ j : Fin 18,
    205467 ≤ acceleratedOrbit j.val 205467 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_205467 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 205467) = 177147 * m + 138848 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 205467
  rw [data_18_205467.1, data_18_205467.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_205467 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 205467) < 262144 * m + 205467 := by
  apply descent_of_endpoint
  · rw [data_18_205467.1]; exact data_18_205467.2.2
  · rw [data_18_205467.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 205915). -/
theorem data_18_205915 : oddCount 205915 18 = 11 ∧
    acceleratedOrbit 18 205915 = 139151 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_205915 : ∀ j : Fin 18,
    205915 ≤ acceleratedOrbit j.val 205915 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_205915 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 205915) = 177147 * m + 139151 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 205915
  rw [data_18_205915.1, data_18_205915.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_205915 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 205915) < 262144 * m + 205915 := by
  apply descent_of_endpoint
  · rw [data_18_205915.1]; exact data_18_205915.2.2
  · rw [data_18_205915.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 206959). -/
theorem data_18_206959 : oddCount 206959 18 = 11 ∧
    acceleratedOrbit 18 206959 = 139856 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_206959 : ∀ j : Fin 18,
    206959 ≤ acceleratedOrbit j.val 206959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_206959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 206959) = 177147 * m + 139856 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 206959
  rw [data_18_206959.1, data_18_206959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_206959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 206959) < 262144 * m + 206959 := by
  apply descent_of_endpoint
  · rw [data_18_206959.1]; exact data_18_206959.2.2
  · rw [data_18_206959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 207015). -/
theorem data_18_207015 : oddCount 207015 18 = 11 ∧
    acceleratedOrbit 18 207015 = 139894 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_207015 : ∀ j : Fin 18,
    207015 ≤ acceleratedOrbit j.val 207015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_207015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207015) = 177147 * m + 139894 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 207015
  rw [data_18_207015.1, data_18_207015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_207015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207015) < 262144 * m + 207015 := by
  apply descent_of_endpoint
  · rw [data_18_207015.1]; exact data_18_207015.2.2
  · rw [data_18_207015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 207099). -/
theorem data_18_207099 : oddCount 207099 18 = 11 ∧
    acceleratedOrbit 18 207099 = 139951 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_207099 : ∀ j : Fin 18,
    207099 ≤ acceleratedOrbit j.val 207099 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_207099 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207099) = 177147 * m + 139951 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 207099
  rw [data_18_207099.1, data_18_207099.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_207099 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207099) < 262144 * m + 207099 := by
  apply descent_of_endpoint
  · rw [data_18_207099.1]; exact data_18_207099.2.2
  · rw [data_18_207099.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 207451). -/
theorem data_18_207451 : oddCount 207451 18 = 11 ∧
    acceleratedOrbit 18 207451 = 140189 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_207451 : ∀ j : Fin 18,
    207451 ≤ acceleratedOrbit j.val 207451 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_207451 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207451) = 177147 * m + 140189 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 207451
  rw [data_18_207451.1, data_18_207451.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_207451 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207451) < 262144 * m + 207451 := by
  apply descent_of_endpoint
  · rw [data_18_207451.1]; exact data_18_207451.2.2
  · rw [data_18_207451.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 207611). -/
theorem data_18_207611 : oddCount 207611 18 = 11 ∧
    acceleratedOrbit 18 207611 = 140297 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_207611 : ∀ j : Fin 18,
    207611 ≤ acceleratedOrbit j.val 207611 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_207611 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207611) = 177147 * m + 140297 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 207611
  rw [data_18_207611.1, data_18_207611.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_207611 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207611) < 262144 * m + 207611 := by
  apply descent_of_endpoint
  · rw [data_18_207611.1]; exact data_18_207611.2.2
  · rw [data_18_207611.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 207807). -/
theorem data_18_207807 : oddCount 207807 18 = 11 ∧
    acceleratedOrbit 18 207807 = 140429 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_207807 : ∀ j : Fin 18,
    207807 ≤ acceleratedOrbit j.val 207807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_207807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207807) = 177147 * m + 140429 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 207807
  rw [data_18_207807.1, data_18_207807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_207807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 207807) < 262144 * m + 207807 := by
  apply descent_of_endpoint
  · rw [data_18_207807.1]; exact data_18_207807.2.2
  · rw [data_18_207807.2.1]; decide

end Collatz.Research.FirstDescent.Batch194
