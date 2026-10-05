import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 150. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch150
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 105983). -/
theorem data_18_105983 : oddCount 105983 18 = 11 ∧
    acceleratedOrbit 18 105983 = 71620 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_105983 : ∀ j : Fin 18,
    105983 ≤ acceleratedOrbit j.val 105983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_105983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105983) = 177147 * m + 71620 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 105983
  rw [data_18_105983.1, data_18_105983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_105983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 105983) < 262144 * m + 105983 := by
  apply descent_of_endpoint
  · rw [data_18_105983.1]; exact data_18_105983.2.2
  · rw [data_18_105983.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 106015). -/
theorem data_18_106015 : oddCount 106015 18 = 11 ∧
    acceleratedOrbit 18 106015 = 71642 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_106015 : ∀ j : Fin 18,
    106015 ≤ acceleratedOrbit j.val 106015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_106015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 106015) = 177147 * m + 71642 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 106015
  rw [data_18_106015.1, data_18_106015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_106015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 106015) < 262144 * m + 106015 := by
  apply descent_of_endpoint
  · rw [data_18_106015.1]; exact data_18_106015.2.2
  · rw [data_18_106015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 106139). -/
theorem data_18_106139 : oddCount 106139 18 = 11 ∧
    acceleratedOrbit 18 106139 = 71726 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_106139 : ∀ j : Fin 18,
    106139 ≤ acceleratedOrbit j.val 106139 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_106139 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 106139) = 177147 * m + 71726 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 106139
  rw [data_18_106139.1, data_18_106139.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_106139 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 106139) < 262144 * m + 106139 := by
  apply descent_of_endpoint
  · rw [data_18_106139.1]; exact data_18_106139.2.2
  · rw [data_18_106139.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 106175). -/
theorem data_18_106175 : oddCount 106175 18 = 11 ∧
    acceleratedOrbit 18 106175 = 71750 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_106175 : ∀ j : Fin 18,
    106175 ≤ acceleratedOrbit j.val 106175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_106175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 106175) = 177147 * m + 71750 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 106175
  rw [data_18_106175.1, data_18_106175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_106175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 106175) < 262144 * m + 106175 := by
  apply descent_of_endpoint
  · rw [data_18_106175.1]; exact data_18_106175.2.2
  · rw [data_18_106175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 107263). -/
theorem data_18_107263 : oddCount 107263 18 = 11 ∧
    acceleratedOrbit 18 107263 = 72485 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_107263 : ∀ j : Fin 18,
    107263 ≤ acceleratedOrbit j.val 107263 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_107263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 107263) = 177147 * m + 72485 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 107263
  rw [data_18_107263.1, data_18_107263.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_107263 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 107263) < 262144 * m + 107263 := by
  apply descent_of_endpoint
  · rw [data_18_107263.1]; exact data_18_107263.2.2
  · rw [data_18_107263.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 107519). -/
theorem data_18_107519 : oddCount 107519 18 = 11 ∧
    acceleratedOrbit 18 107519 = 72658 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_107519 : ∀ j : Fin 18,
    107519 ≤ acceleratedOrbit j.val 107519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_107519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 107519) = 177147 * m + 72658 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 107519
  rw [data_18_107519.1, data_18_107519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_107519 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 107519) < 262144 * m + 107519 := by
  apply descent_of_endpoint
  · rw [data_18_107519.1]; exact data_18_107519.2.2
  · rw [data_18_107519.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 107771). -/
theorem data_18_107771 : oddCount 107771 18 = 11 ∧
    acceleratedOrbit 18 107771 = 72829 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_107771 : ∀ j : Fin 18,
    107771 ≤ acceleratedOrbit j.val 107771 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_107771 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 107771) = 177147 * m + 72829 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 107771
  rw [data_18_107771.1, data_18_107771.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_107771 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 107771) < 262144 * m + 107771 := by
  apply descent_of_endpoint
  · rw [data_18_107771.1]; exact data_18_107771.2.2
  · rw [data_18_107771.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 108031). -/
theorem data_18_108031 : oddCount 108031 18 = 11 ∧
    acceleratedOrbit 18 108031 = 73004 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_108031 : ∀ j : Fin 18,
    108031 ≤ acceleratedOrbit j.val 108031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_108031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108031) = 177147 * m + 73004 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 108031
  rw [data_18_108031.1, data_18_108031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_108031 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 108031) < 262144 * m + 108031 := by
  apply descent_of_endpoint
  · rw [data_18_108031.1]; exact data_18_108031.2.2
  · rw [data_18_108031.2.1]; decide

end Collatz.Research.FirstDescent.Batch150
