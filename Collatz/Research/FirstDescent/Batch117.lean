import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 117. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch117
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 38447). -/
theorem data_18_38447 : oddCount 38447 18 = 11 ∧
    acceleratedOrbit 18 38447 = 25982 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_38447 : ∀ j : Fin 18,
    38447 ≤ acceleratedOrbit j.val 38447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_38447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38447) = 177147 * m + 25982 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 38447
  rw [data_18_38447.1, data_18_38447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_38447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38447) < 262144 * m + 38447 := by
  apply descent_of_endpoint
  · rw [data_18_38447.1]; exact data_18_38447.2.2
  · rw [data_18_38447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 38503). -/
theorem data_18_38503 : oddCount 38503 18 = 11 ∧
    acceleratedOrbit 18 38503 = 26020 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_38503 : ∀ j : Fin 18,
    38503 ≤ acceleratedOrbit j.val 38503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_38503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38503) = 177147 * m + 26020 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 38503
  rw [data_18_38503.1, data_18_38503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_38503 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38503) < 262144 * m + 38503 := by
  apply descent_of_endpoint
  · rw [data_18_38503.1]; exact data_18_38503.2.2
  · rw [data_18_38503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 38783). -/
theorem data_18_38783 : oddCount 38783 18 = 11 ∧
    acceleratedOrbit 18 38783 = 26209 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_38783 : ∀ j : Fin 18,
    38783 ≤ acceleratedOrbit j.val 38783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_38783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38783) = 177147 * m + 26209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 38783
  rw [data_18_38783.1, data_18_38783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_38783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38783) < 262144 * m + 38783 := by
  apply descent_of_endpoint
  · rw [data_18_38783.1]; exact data_18_38783.2.2
  · rw [data_18_38783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 38975). -/
theorem data_18_38975 : oddCount 38975 18 = 11 ∧
    acceleratedOrbit 18 38975 = 26339 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_38975 : ∀ j : Fin 18,
    38975 ≤ acceleratedOrbit j.val 38975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_38975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38975) = 177147 * m + 26339 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 38975
  rw [data_18_38975.1, data_18_38975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_38975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 38975) < 262144 * m + 38975 := by
  apply descent_of_endpoint
  · rw [data_18_38975.1]; exact data_18_38975.2.2
  · rw [data_18_38975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 39015). -/
theorem data_18_39015 : oddCount 39015 18 = 11 ∧
    acceleratedOrbit 18 39015 = 26366 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_39015 : ∀ j : Fin 18,
    39015 ≤ acceleratedOrbit j.val 39015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_39015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 39015) = 177147 * m + 26366 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 39015
  rw [data_18_39015.1, data_18_39015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_39015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 39015) < 262144 * m + 39015 := by
  apply descent_of_endpoint
  · rw [data_18_39015.1]; exact data_18_39015.2.2
  · rw [data_18_39015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 39743). -/
theorem data_18_39743 : oddCount 39743 18 = 11 ∧
    acceleratedOrbit 18 39743 = 26858 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_39743 : ∀ j : Fin 18,
    39743 ≤ acceleratedOrbit j.val 39743 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_39743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 39743) = 177147 * m + 26858 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 39743
  rw [data_18_39743.1, data_18_39743.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_39743 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 39743) < 262144 * m + 39743 := by
  apply descent_of_endpoint
  · rw [data_18_39743.1]; exact data_18_39743.2.2
  · rw [data_18_39743.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 39783). -/
theorem data_18_39783 : oddCount 39783 18 = 11 ∧
    acceleratedOrbit 18 39783 = 26885 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_39783 : ∀ j : Fin 18,
    39783 ≤ acceleratedOrbit j.val 39783 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_39783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 39783) = 177147 * m + 26885 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 39783
  rw [data_18_39783.1, data_18_39783.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_39783 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 39783) < 262144 * m + 39783 := by
  apply descent_of_endpoint
  · rw [data_18_39783.1]; exact data_18_39783.2.2
  · rw [data_18_39783.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 40767). -/
theorem data_18_40767 : oddCount 40767 18 = 11 ∧
    acceleratedOrbit 18 40767 = 27550 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_40767 : ∀ j : Fin 18,
    40767 ≤ acceleratedOrbit j.val 40767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_40767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 40767) = 177147 * m + 27550 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 40767
  rw [data_18_40767.1, data_18_40767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_40767 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 40767) < 262144 * m + 40767 := by
  apply descent_of_endpoint
  · rw [data_18_40767.1]; exact data_18_40767.2.2
  · rw [data_18_40767.2.1]; decide

end Collatz.Research.FirstDescent.Batch117
