import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 170. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch170
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 150559). -/
theorem data_18_150559 : oddCount 150559 18 = 11 ∧
    acceleratedOrbit 18 150559 = 101743 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_150559 : ∀ j : Fin 18,
    150559 ≤ acceleratedOrbit j.val 150559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_150559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 150559) = 177147 * m + 101743 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 150559
  rw [data_18_150559.1, data_18_150559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_150559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 150559) < 262144 * m + 150559 := by
  apply descent_of_endpoint
  · rw [data_18_150559.1]; exact data_18_150559.2.2
  · rw [data_18_150559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 151195). -/
theorem data_18_151195 : oddCount 151195 18 = 11 ∧
    acceleratedOrbit 18 151195 = 102173 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_151195 : ∀ j : Fin 18,
    151195 ≤ acceleratedOrbit j.val 151195 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_151195 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151195) = 177147 * m + 102173 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 151195
  rw [data_18_151195.1, data_18_151195.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_151195 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151195) < 262144 * m + 151195 := by
  apply descent_of_endpoint
  · rw [data_18_151195.1]; exact data_18_151195.2.2
  · rw [data_18_151195.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 151643). -/
theorem data_18_151643 : oddCount 151643 18 = 11 ∧
    acceleratedOrbit 18 151643 = 102476 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_151643 : ∀ j : Fin 18,
    151643 ≤ acceleratedOrbit j.val 151643 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_151643 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151643) = 177147 * m + 102476 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 151643
  rw [data_18_151643.1, data_18_151643.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_151643 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151643) < 262144 * m + 151643 := by
  apply descent_of_endpoint
  · rw [data_18_151643.1]; exact data_18_151643.2.2
  · rw [data_18_151643.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 151719). -/
theorem data_18_151719 : oddCount 151719 18 = 11 ∧
    acceleratedOrbit 18 151719 = 102527 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_151719 : ∀ j : Fin 18,
    151719 ≤ acceleratedOrbit j.val 151719 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_151719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151719) = 177147 * m + 102527 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 151719
  rw [data_18_151719.1, data_18_151719.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_151719 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151719) < 262144 * m + 151719 := by
  apply descent_of_endpoint
  · rw [data_18_151719.1]; exact data_18_151719.2.2
  · rw [data_18_151719.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 151775). -/
theorem data_18_151775 : oddCount 151775 18 = 11 ∧
    acceleratedOrbit 18 151775 = 102565 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_151775 : ∀ j : Fin 18,
    151775 ≤ acceleratedOrbit j.val 151775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_151775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151775) = 177147 * m + 102565 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 151775
  rw [data_18_151775.1, data_18_151775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_151775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 151775) < 262144 * m + 151775 := by
  apply descent_of_endpoint
  · rw [data_18_151775.1]; exact data_18_151775.2.2
  · rw [data_18_151775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 152255). -/
theorem data_18_152255 : oddCount 152255 18 = 11 ∧
    acceleratedOrbit 18 152255 = 102889 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_152255 : ∀ j : Fin 18,
    152255 ≤ acceleratedOrbit j.val 152255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_152255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 152255) = 177147 * m + 102889 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 152255
  rw [data_18_152255.1, data_18_152255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_152255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 152255) < 262144 * m + 152255 := by
  apply descent_of_endpoint
  · rw [data_18_152255.1]; exact data_18_152255.2.2
  · rw [data_18_152255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 152607). -/
theorem data_18_152607 : oddCount 152607 18 = 11 ∧
    acceleratedOrbit 18 152607 = 103127 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_152607 : ∀ j : Fin 18,
    152607 ≤ acceleratedOrbit j.val 152607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_152607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 152607) = 177147 * m + 103127 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 152607
  rw [data_18_152607.1, data_18_152607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_152607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 152607) < 262144 * m + 152607 := by
  apply descent_of_endpoint
  · rw [data_18_152607.1]; exact data_18_152607.2.2
  · rw [data_18_152607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 153055). -/
theorem data_18_153055 : oddCount 153055 18 = 11 ∧
    acceleratedOrbit 18 153055 = 103430 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_153055 : ∀ j : Fin 18,
    153055 ≤ acceleratedOrbit j.val 153055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_153055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 153055) = 177147 * m + 103430 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 153055
  rw [data_18_153055.1, data_18_153055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_153055 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 153055) < 262144 * m + 153055 := by
  apply descent_of_endpoint
  · rw [data_18_153055.1]; exact data_18_153055.2.2
  · rw [data_18_153055.2.1]; decide

end Collatz.Research.FirstDescent.Batch170
