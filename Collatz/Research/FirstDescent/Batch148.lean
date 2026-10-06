import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 148. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch148
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 104415). -/
theorem data_18_104415 : oddCount 104415 18 = 11 ∧
    acceleratedOrbit 18 104415 = 70561 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_104415 : ∀ j : Fin 18,
    104415 ≤ acceleratedOrbit j.val 104415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_104415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104415) = 177147 * m + 70561 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 104415
  rw [data_18_104415.1, data_18_104415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_104415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104415) < 262144 * m + 104415 := by
  apply descent_of_endpoint
  · rw [data_18_104415.1]; exact data_18_104415.2.2
  · rw [data_18_104415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 104447). -/
theorem data_18_104447 : oddCount 104447 18 = 11 ∧
    acceleratedOrbit 18 104447 = 70582 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_104447 : ∀ j : Fin 18,
    104447 ≤ acceleratedOrbit j.val 104447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_104447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104447) = 177147 * m + 70582 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 104447
  rw [data_18_104447.1, data_18_104447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_104447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104447) < 262144 * m + 104447 := by
  apply descent_of_endpoint
  · rw [data_18_104447.1]; exact data_18_104447.2.2
  · rw [data_18_104447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 104495). -/
theorem data_18_104495 : oddCount 104495 18 = 11 ∧
    acceleratedOrbit 18 104495 = 70615 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_104495 : ∀ j : Fin 18,
    104495 ≤ acceleratedOrbit j.val 104495 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_104495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104495) = 177147 * m + 70615 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 104495
  rw [data_18_104495.1, data_18_104495.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_104495 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104495) < 262144 * m + 104495 := by
  apply descent_of_endpoint
  · rw [data_18_104495.1]; exact data_18_104495.2.2
  · rw [data_18_104495.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 104615). -/
theorem data_18_104615 : oddCount 104615 18 = 11 ∧
    acceleratedOrbit 18 104615 = 70696 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_104615 : ∀ j : Fin 18,
    104615 ≤ acceleratedOrbit j.val 104615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_104615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104615) = 177147 * m + 70696 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 104615
  rw [data_18_104615.1, data_18_104615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_104615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104615) < 262144 * m + 104615 := by
  apply descent_of_endpoint
  · rw [data_18_104615.1]; exact data_18_104615.2.2
  · rw [data_18_104615.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 104959). -/
theorem data_18_104959 : oddCount 104959 18 = 11 ∧
    acceleratedOrbit 18 104959 = 70928 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_104959 : ∀ j : Fin 18,
    104959 ≤ acceleratedOrbit j.val 104959 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_104959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104959) = 177147 * m + 70928 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 104959
  rw [data_18_104959.1, data_18_104959.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_104959 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 104959) < 262144 * m + 104959 := by
  apply descent_of_endpoint
  · rw [data_18_104959.1]; exact data_18_104959.2.2
  · rw [data_18_104959.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105007). -/
theorem data_18_105007 : oddCount 105007 18 = 11 ∧
    acceleratedOrbit 18 105007 = 70961 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105007 : ∀ j : Fin 18,
    105007 ≤ acceleratedOrbit j.val 105007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105007) = 177147 * m + 70961 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105007
  rw [data_18_105007.1, data_18_105007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105007) < 262144 * m + 105007 := by
  apply descent_of_endpoint
  · rw [data_18_105007.1]; exact data_18_105007.2.2
  · rw [data_18_105007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105127). -/
theorem data_18_105127 : oddCount 105127 18 = 11 ∧
    acceleratedOrbit 18 105127 = 71042 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105127 : ∀ j : Fin 18,
    105127 ≤ acceleratedOrbit j.val 105127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105127) = 177147 * m + 71042 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105127
  rw [data_18_105127.1, data_18_105127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105127 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105127) < 262144 * m + 105127 := by
  apply descent_of_endpoint
  · rw [data_18_105127.1]; exact data_18_105127.2.2
  · rw [data_18_105127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105167). -/
theorem data_18_105167 : oddCount 105167 18 = 11 ∧
    acceleratedOrbit 18 105167 = 71069 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105167 : ∀ j : Fin 18,
    105167 ≤ acceleratedOrbit j.val 105167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105167) = 177147 * m + 71069 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105167
  rw [data_18_105167.1, data_18_105167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105167) < 262144 * m + 105167 := by
  apply descent_of_endpoint
  · rw [data_18_105167.1]; exact data_18_105167.2.2
  · rw [data_18_105167.2.1]; decide

end Collatz.Research.FirstDescent.Batch148
