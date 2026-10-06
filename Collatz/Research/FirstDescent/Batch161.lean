import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 161. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch161
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 126831). -/
theorem data_18_126831 : oddCount 126831 18 = 11 ∧
    acceleratedOrbit 18 126831 = 85709 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_126831 : ∀ j : Fin 18,
    126831 ≤ acceleratedOrbit j.val 126831 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_126831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126831) = 177147 * m + 85709 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 126831
  rw [data_18_126831.1, data_18_126831.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_126831 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126831) < 262144 * m + 126831 := by
  apply descent_of_endpoint
  · rw [data_18_126831.1]; exact data_18_126831.2.2
  · rw [data_18_126831.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 126879). -/
theorem data_18_126879 : oddCount 126879 18 = 11 ∧
    acceleratedOrbit 18 126879 = 85741 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_126879 : ∀ j : Fin 18,
    126879 ≤ acceleratedOrbit j.val 126879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_126879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126879) = 177147 * m + 85741 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 126879
  rw [data_18_126879.1, data_18_126879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_126879 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126879) < 262144 * m + 126879 := by
  apply descent_of_endpoint
  · rw [data_18_126879.1]; exact data_18_126879.2.2
  · rw [data_18_126879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 127003). -/
theorem data_18_127003 : oddCount 127003 18 = 11 ∧
    acceleratedOrbit 18 127003 = 85825 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_127003 : ∀ j : Fin 18,
    127003 ≤ acceleratedOrbit j.val 127003 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_127003 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 127003) = 177147 * m + 85825 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 127003
  rw [data_18_127003.1, data_18_127003.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_127003 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 127003) < 262144 * m + 127003 := by
  apply descent_of_endpoint
  · rw [data_18_127003.1]; exact data_18_127003.2.2
  · rw [data_18_127003.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 127231). -/
theorem data_18_127231 : oddCount 127231 18 = 11 ∧
    acceleratedOrbit 18 127231 = 85979 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_127231 : ∀ j : Fin 18,
    127231 ≤ acceleratedOrbit j.val 127231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_127231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 127231) = 177147 * m + 85979 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 127231
  rw [data_18_127231.1, data_18_127231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_127231 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 127231) < 262144 * m + 127231 := by
  apply descent_of_endpoint
  · rw [data_18_127231.1]; exact data_18_127231.2.2
  · rw [data_18_127231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 127391). -/
theorem data_18_127391 : oddCount 127391 18 = 11 ∧
    acceleratedOrbit 18 127391 = 86087 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_127391 : ∀ j : Fin 18,
    127391 ≤ acceleratedOrbit j.val 127391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_127391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 127391) = 177147 * m + 86087 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 127391
  rw [data_18_127391.1, data_18_127391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_127391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 127391) < 262144 * m + 127391 := by
  apply descent_of_endpoint
  · rw [data_18_127391.1]; exact data_18_127391.2.2
  · rw [data_18_127391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 129307). -/
theorem data_18_129307 : oddCount 129307 18 = 11 ∧
    acceleratedOrbit 18 129307 = 87382 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_129307 : ∀ j : Fin 18,
    129307 ≤ acceleratedOrbit j.val 129307 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_129307 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 129307) = 177147 * m + 87382 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 129307
  rw [data_18_129307.1, data_18_129307.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_129307 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 129307) < 262144 * m + 129307 := by
  apply descent_of_endpoint
  · rw [data_18_129307.1]; exact data_18_129307.2.2
  · rw [data_18_129307.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 129343). -/
theorem data_18_129343 : oddCount 129343 18 = 11 ∧
    acceleratedOrbit 18 129343 = 87406 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_129343 : ∀ j : Fin 18,
    129343 ≤ acceleratedOrbit j.val 129343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_129343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 129343) = 177147 * m + 87406 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 129343
  rw [data_18_129343.1, data_18_129343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_129343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 129343) < 262144 * m + 129343 := by
  apply descent_of_endpoint
  · rw [data_18_129343.1]; exact data_18_129343.2.2
  · rw [data_18_129343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 129775). -/
theorem data_18_129775 : oddCount 129775 18 = 11 ∧
    acceleratedOrbit 18 129775 = 87698 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_129775 : ∀ j : Fin 18,
    129775 ≤ acceleratedOrbit j.val 129775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_129775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 129775) = 177147 * m + 87698 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 129775
  rw [data_18_129775.1, data_18_129775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_129775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 129775) < 262144 * m + 129775 := by
  apply descent_of_endpoint
  · rw [data_18_129775.1]; exact data_18_129775.2.2
  · rw [data_18_129775.2.1]; decide

end Collatz.Research.FirstDescent.Batch161
