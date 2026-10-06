import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 120. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch120
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 45759). -/
theorem data_18_45759 : oddCount 45759 18 = 11 ∧
    acceleratedOrbit 18 45759 = 30923 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_45759 : ∀ j : Fin 18,
    45759 ≤ acceleratedOrbit j.val 45759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_45759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 45759) = 177147 * m + 30923 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 45759
  rw [data_18_45759.1, data_18_45759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_45759 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 45759) < 262144 * m + 45759 := by
  apply descent_of_endpoint
  · rw [data_18_45759.1]; exact data_18_45759.2.2
  · rw [data_18_45759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 46015). -/
theorem data_18_46015 : oddCount 46015 18 = 11 ∧
    acceleratedOrbit 18 46015 = 31096 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_46015 : ∀ j : Fin 18,
    46015 ≤ acceleratedOrbit j.val 46015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_46015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46015) = 177147 * m + 31096 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 46015
  rw [data_18_46015.1, data_18_46015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_46015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46015) < 262144 * m + 46015 := by
  apply descent_of_endpoint
  · rw [data_18_46015.1]; exact data_18_46015.2.2
  · rw [data_18_46015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 46047). -/
theorem data_18_46047 : oddCount 46047 18 = 11 ∧
    acceleratedOrbit 18 46047 = 31118 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_46047 : ∀ j : Fin 18,
    46047 ≤ acceleratedOrbit j.val 46047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_46047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46047) = 177147 * m + 31118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 46047
  rw [data_18_46047.1, data_18_46047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_46047 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46047) < 262144 * m + 46047 := by
  apply descent_of_endpoint
  · rw [data_18_46047.1]; exact data_18_46047.2.2
  · rw [data_18_46047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 46695). -/
theorem data_18_46695 : oddCount 46695 18 = 11 ∧
    acceleratedOrbit 18 46695 = 31556 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_46695 : ∀ j : Fin 18,
    46695 ≤ acceleratedOrbit j.val 46695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_46695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46695) = 177147 * m + 31556 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 46695
  rw [data_18_46695.1, data_18_46695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_46695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46695) < 262144 * m + 46695 := by
  apply descent_of_endpoint
  · rw [data_18_46695.1]; exact data_18_46695.2.2
  · rw [data_18_46695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 46975). -/
theorem data_18_46975 : oddCount 46975 18 = 11 ∧
    acceleratedOrbit 18 46975 = 31745 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_46975 : ∀ j : Fin 18,
    46975 ≤ acceleratedOrbit j.val 46975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_46975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46975) = 177147 * m + 31745 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 46975
  rw [data_18_46975.1, data_18_46975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_46975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 46975) < 262144 * m + 46975 := by
  apply descent_of_endpoint
  · rw [data_18_46975.1]; exact data_18_46975.2.2
  · rw [data_18_46975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 47355). -/
theorem data_18_47355 : oddCount 47355 18 = 11 ∧
    acceleratedOrbit 18 47355 = 32002 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_47355 : ∀ j : Fin 18,
    47355 ≤ acceleratedOrbit j.val 47355 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_47355 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 47355) = 177147 * m + 32002 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 47355
  rw [data_18_47355.1, data_18_47355.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_47355 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 47355) < 262144 * m + 47355 := by
  apply descent_of_endpoint
  · rw [data_18_47355.1]; exact data_18_47355.2.2
  · rw [data_18_47355.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 47719). -/
theorem data_18_47719 : oddCount 47719 18 = 11 ∧
    acceleratedOrbit 18 47719 = 32248 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_47719 : ∀ j : Fin 18,
    47719 ≤ acceleratedOrbit j.val 47719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_47719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 47719) = 177147 * m + 32248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 47719
  rw [data_18_47719.1, data_18_47719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_47719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 47719) < 262144 * m + 47719 := by
  apply descent_of_endpoint
  · rw [data_18_47719.1]; exact data_18_47719.2.2
  · rw [data_18_47719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 48159). -/
theorem data_18_48159 : oddCount 48159 18 = 11 ∧
    acceleratedOrbit 18 48159 = 32545 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_48159 : ∀ j : Fin 18,
    48159 ≤ acceleratedOrbit j.val 48159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_48159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48159) = 177147 * m + 32545 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 48159
  rw [data_18_48159.1, data_18_48159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_48159 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 48159) < 262144 * m + 48159 := by
  apply descent_of_endpoint
  · rw [data_18_48159.1]; exact data_18_48159.2.2
  · rw [data_18_48159.2.1]; decide

end Collatz.Research.FirstDescent.Batch120
