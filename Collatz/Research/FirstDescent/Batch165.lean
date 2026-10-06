import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 165. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch165
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 137695). -/
theorem data_18_137695 : oddCount 137695 18 = 11 ∧
    acceleratedOrbit 18 137695 = 93050 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_137695 : ∀ j : Fin 18,
    137695 ≤ acceleratedOrbit j.val 137695 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_137695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 137695) = 177147 * m + 93050 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 137695
  rw [data_18_137695.1, data_18_137695.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_137695 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 137695) < 262144 * m + 137695 := by
  apply descent_of_endpoint
  · rw [data_18_137695.1]; exact data_18_137695.2.2
  · rw [data_18_137695.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 138111). -/
theorem data_18_138111 : oddCount 138111 18 = 11 ∧
    acceleratedOrbit 18 138111 = 93331 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_138111 : ∀ j : Fin 18,
    138111 ≤ acceleratedOrbit j.val 138111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_138111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138111) = 177147 * m + 93331 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 138111
  rw [data_18_138111.1, data_18_138111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_138111 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138111) < 262144 * m + 138111 := by
  apply descent_of_endpoint
  · rw [data_18_138111.1]; exact data_18_138111.2.2
  · rw [data_18_138111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 138223). -/
theorem data_18_138223 : oddCount 138223 18 = 11 ∧
    acceleratedOrbit 18 138223 = 93407 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_138223 : ∀ j : Fin 18,
    138223 ≤ acceleratedOrbit j.val 138223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_138223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138223) = 177147 * m + 93407 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 138223
  rw [data_18_138223.1, data_18_138223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_138223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138223) < 262144 * m + 138223 := by
  apply descent_of_endpoint
  · rw [data_18_138223.1]; exact data_18_138223.2.2
  · rw [data_18_138223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 138343). -/
theorem data_18_138343 : oddCount 138343 18 = 11 ∧
    acceleratedOrbit 18 138343 = 93488 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_138343 : ∀ j : Fin 18,
    138343 ≤ acceleratedOrbit j.val 138343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_138343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138343) = 177147 * m + 93488 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 138343
  rw [data_18_138343.1, data_18_138343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_138343 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138343) < 262144 * m + 138343 := by
  apply descent_of_endpoint
  · rw [data_18_138343.1]; exact data_18_138343.2.2
  · rw [data_18_138343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 138991). -/
theorem data_18_138991 : oddCount 138991 18 = 11 ∧
    acceleratedOrbit 18 138991 = 93926 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_138991 : ∀ j : Fin 18,
    138991 ≤ acceleratedOrbit j.val 138991 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_138991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138991) = 177147 * m + 93926 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 138991
  rw [data_18_138991.1, data_18_138991.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_138991 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 138991) < 262144 * m + 138991 := by
  apply descent_of_endpoint
  · rw [data_18_138991.1]; exact data_18_138991.2.2
  · rw [data_18_138991.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 139355). -/
theorem data_18_139355 : oddCount 139355 18 = 11 ∧
    acceleratedOrbit 18 139355 = 94172 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_139355 : ∀ j : Fin 18,
    139355 ≤ acceleratedOrbit j.val 139355 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_139355 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 139355) = 177147 * m + 94172 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 139355
  rw [data_18_139355.1, data_18_139355.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_139355 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 139355) < 262144 * m + 139355 := by
  apply descent_of_endpoint
  · rw [data_18_139355.1]; exact data_18_139355.2.2
  · rw [data_18_139355.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 140095). -/
theorem data_18_140095 : oddCount 140095 18 = 11 ∧
    acceleratedOrbit 18 140095 = 94672 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_140095 : ∀ j : Fin 18,
    140095 ≤ acceleratedOrbit j.val 140095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_140095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140095) = 177147 * m + 94672 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 140095
  rw [data_18_140095.1, data_18_140095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_140095 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140095) < 262144 * m + 140095 := by
  apply descent_of_endpoint
  · rw [data_18_140095.1]; exact data_18_140095.2.2
  · rw [data_18_140095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 140415). -/
theorem data_18_140415 : oddCount 140415 18 = 11 ∧
    acceleratedOrbit 18 140415 = 94888 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_140415 : ∀ j : Fin 18,
    140415 ≤ acceleratedOrbit j.val 140415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_140415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140415) = 177147 * m + 94888 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 140415
  rw [data_18_140415.1, data_18_140415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_140415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 140415) < 262144 * m + 140415 := by
  apply descent_of_endpoint
  · rw [data_18_140415.1]; exact data_18_140415.2.2
  · rw [data_18_140415.2.1]; decide

end Collatz.Research.FirstDescent.Batch165
