import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 128. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch128
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 60159). -/
theorem data_18_60159 : oddCount 60159 18 = 11 ∧
    acceleratedOrbit 18 60159 = 40654 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_60159 : ∀ j : Fin 18,
    60159 ≤ acceleratedOrbit j.val 60159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_60159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60159) = 177147 * m + 40654 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 60159
  rw [data_18_60159.1, data_18_60159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_60159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60159) < 262144 * m + 60159 := by
  apply descent_of_endpoint
  · rw [data_18_60159.1]; exact data_18_60159.2.2
  · rw [data_18_60159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 60191). -/
theorem data_18_60191 : oddCount 60191 18 = 11 ∧
    acceleratedOrbit 18 60191 = 40676 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_60191 : ∀ j : Fin 18,
    60191 ≤ acceleratedOrbit j.val 60191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_60191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60191) = 177147 * m + 40676 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 60191
  rw [data_18_60191.1, data_18_60191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_60191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60191) < 262144 * m + 60191 := by
  apply descent_of_endpoint
  · rw [data_18_60191.1]; exact data_18_60191.2.2
  · rw [data_18_60191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 60671). -/
theorem data_18_60671 : oddCount 60671 18 = 11 ∧
    acceleratedOrbit 18 60671 = 41000 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_60671 : ∀ j : Fin 18,
    60671 ≤ acceleratedOrbit j.val 60671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_60671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60671) = 177147 * m + 41000 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 60671
  rw [data_18_60671.1, data_18_60671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_60671 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60671) < 262144 * m + 60671 := by
  apply descent_of_endpoint
  · rw [data_18_60671.1]; exact data_18_60671.2.2
  · rw [data_18_60671.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 60719). -/
theorem data_18_60719 : oddCount 60719 18 = 11 ∧
    acceleratedOrbit 18 60719 = 41033 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_60719 : ∀ j : Fin 18,
    60719 ≤ acceleratedOrbit j.val 60719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_60719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60719) = 177147 * m + 41033 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 60719
  rw [data_18_60719.1, data_18_60719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_60719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60719) < 262144 * m + 60719 := by
  apply descent_of_endpoint
  · rw [data_18_60719.1]; exact data_18_60719.2.2
  · rw [data_18_60719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 60959). -/
theorem data_18_60959 : oddCount 60959 18 = 11 ∧
    acceleratedOrbit 18 60959 = 41195 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_60959 : ∀ j : Fin 18,
    60959 ≤ acceleratedOrbit j.val 60959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_60959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60959) = 177147 * m + 41195 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 60959
  rw [data_18_60959.1, data_18_60959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_60959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 60959) < 262144 * m + 60959 := by
  apply descent_of_endpoint
  · rw [data_18_60959.1]; exact data_18_60959.2.2
  · rw [data_18_60959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 61119). -/
theorem data_18_61119 : oddCount 61119 18 = 11 ∧
    acceleratedOrbit 18 61119 = 41303 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_61119 : ∀ j : Fin 18,
    61119 ≤ acceleratedOrbit j.val 61119 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_61119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 61119) = 177147 * m + 41303 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 61119
  rw [data_18_61119.1, data_18_61119.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_61119 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 61119) < 262144 * m + 61119 := by
  apply descent_of_endpoint
  · rw [data_18_61119.1]; exact data_18_61119.2.2
  · rw [data_18_61119.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 61743). -/
theorem data_18_61743 : oddCount 61743 18 = 11 ∧
    acceleratedOrbit 18 61743 = 41725 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_61743 : ∀ j : Fin 18,
    61743 ≤ acceleratedOrbit j.val 61743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_61743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 61743) = 177147 * m + 41725 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 61743
  rw [data_18_61743.1, data_18_61743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_61743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 61743) < 262144 * m + 61743 := by
  apply descent_of_endpoint
  · rw [data_18_61743.1]; exact data_18_61743.2.2
  · rw [data_18_61743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 61983). -/
theorem data_18_61983 : oddCount 61983 18 = 11 ∧
    acceleratedOrbit 18 61983 = 41887 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_61983 : ∀ j : Fin 18,
    61983 ≤ acceleratedOrbit j.val 61983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_61983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 61983) = 177147 * m + 41887 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 61983
  rw [data_18_61983.1, data_18_61983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_61983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 61983) < 262144 * m + 61983 := by
  apply descent_of_endpoint
  · rw [data_18_61983.1]; exact data_18_61983.2.2
  · rw [data_18_61983.2.1]; decide

end Collatz.Research.FirstDescent.Batch128
