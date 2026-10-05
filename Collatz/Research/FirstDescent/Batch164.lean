import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 164. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch164
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 135195). -/
theorem data_18_135195 : oddCount 135195 18 = 11 ∧
    acceleratedOrbit 18 135195 = 91361 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_135195 : ∀ j : Fin 18,
    135195 ≤ acceleratedOrbit j.val 135195 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_135195 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 135195) = 177147 * m + 91361 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 135195
  rw [data_18_135195.1, data_18_135195.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_135195 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 135195) < 262144 * m + 135195 := by
  apply descent_of_endpoint
  · rw [data_18_135195.1]; exact data_18_135195.2.2
  · rw [data_18_135195.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 135807). -/
theorem data_18_135807 : oddCount 135807 18 = 11 ∧
    acceleratedOrbit 18 135807 = 91774 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_135807 : ∀ j : Fin 18,
    135807 ≤ acceleratedOrbit j.val 135807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_135807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 135807) = 177147 * m + 91774 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 135807
  rw [data_18_135807.1, data_18_135807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_135807 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 135807) < 262144 * m + 135807 := by
  apply descent_of_endpoint
  · rw [data_18_135807.1]; exact data_18_135807.2.2
  · rw [data_18_135807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 136039). -/
theorem data_18_136039 : oddCount 136039 18 = 11 ∧
    acceleratedOrbit 18 136039 = 91931 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_136039 : ∀ j : Fin 18,
    136039 ≤ acceleratedOrbit j.val 136039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_136039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136039) = 177147 * m + 91931 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 136039
  rw [data_18_136039.1, data_18_136039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_136039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136039) < 262144 * m + 136039 := by
  apply descent_of_endpoint
  · rw [data_18_136039.1]; exact data_18_136039.2.2
  · rw [data_18_136039.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 136295). -/
theorem data_18_136295 : oddCount 136295 18 = 11 ∧
    acceleratedOrbit 18 136295 = 92104 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_136295 : ∀ j : Fin 18,
    136295 ≤ acceleratedOrbit j.val 136295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_136295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136295) = 177147 * m + 92104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 136295
  rw [data_18_136295.1, data_18_136295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_136295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136295) < 262144 * m + 136295 := by
  apply descent_of_endpoint
  · rw [data_18_136295.1]; exact data_18_136295.2.2
  · rw [data_18_136295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 136319). -/
theorem data_18_136319 : oddCount 136319 18 = 11 ∧
    acceleratedOrbit 18 136319 = 92120 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_136319 : ∀ j : Fin 18,
    136319 ≤ acceleratedOrbit j.val 136319 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_136319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136319) = 177147 * m + 92120 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 136319
  rw [data_18_136319.1, data_18_136319.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_136319 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136319) < 262144 * m + 136319 := by
  apply descent_of_endpoint
  · rw [data_18_136319.1]; exact data_18_136319.2.2
  · rw [data_18_136319.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 136731). -/
theorem data_18_136731 : oddCount 136731 18 = 11 ∧
    acceleratedOrbit 18 136731 = 92399 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_136731 : ∀ j : Fin 18,
    136731 ≤ acceleratedOrbit j.val 136731 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_136731 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136731) = 177147 * m + 92399 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 136731
  rw [data_18_136731.1, data_18_136731.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_136731 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 136731) < 262144 * m + 136731 := by
  apply descent_of_endpoint
  · rw [data_18_136731.1]; exact data_18_136731.2.2
  · rw [data_18_136731.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 137307). -/
theorem data_18_137307 : oddCount 137307 18 = 11 ∧
    acceleratedOrbit 18 137307 = 92788 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_137307 : ∀ j : Fin 18,
    137307 ≤ acceleratedOrbit j.val 137307 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_137307 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 137307) = 177147 * m + 92788 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 137307
  rw [data_18_137307.1, data_18_137307.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_137307 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 137307) < 262144 * m + 137307 := by
  apply descent_of_endpoint
  · rw [data_18_137307.1]; exact data_18_137307.2.2
  · rw [data_18_137307.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 137499). -/
theorem data_18_137499 : oddCount 137499 18 = 11 ∧
    acceleratedOrbit 18 137499 = 92918 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_137499 : ∀ j : Fin 18,
    137499 ≤ acceleratedOrbit j.val 137499 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_137499 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 137499) = 177147 * m + 92918 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 137499
  rw [data_18_137499.1, data_18_137499.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_137499 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 137499) < 262144 * m + 137499 := by
  apply descent_of_endpoint
  · rw [data_18_137499.1]; exact data_18_137499.2.2
  · rw [data_18_137499.2.1]; decide

end Collatz.Research.FirstDescent.Batch164
