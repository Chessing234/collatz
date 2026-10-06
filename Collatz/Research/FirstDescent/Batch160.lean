import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 160. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch160
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 125391). -/
theorem data_18_125391 : oddCount 125391 18 = 11 ∧
    acceleratedOrbit 18 125391 = 84736 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_125391 : ∀ j : Fin 18,
    125391 ≤ acceleratedOrbit j.val 125391 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_125391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 125391) = 177147 * m + 84736 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 125391
  rw [data_18_125391.1, data_18_125391.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_125391 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 125391) < 262144 * m + 125391 := by
  apply descent_of_endpoint
  · rw [data_18_125391.1]; exact data_18_125391.2.2
  · rw [data_18_125391.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 125863). -/
theorem data_18_125863 : oddCount 125863 18 = 11 ∧
    acceleratedOrbit 18 125863 = 85055 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_125863 : ∀ j : Fin 18,
    125863 ≤ acceleratedOrbit j.val 125863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_125863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 125863) = 177147 * m + 85055 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 125863
  rw [data_18_125863.1, data_18_125863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_125863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 125863) < 262144 * m + 125863 := by
  apply descent_of_endpoint
  · rw [data_18_125863.1]; exact data_18_125863.2.2
  · rw [data_18_125863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 125979). -/
theorem data_18_125979 : oddCount 125979 18 = 11 ∧
    acceleratedOrbit 18 125979 = 85133 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_125979 : ∀ j : Fin 18,
    125979 ≤ acceleratedOrbit j.val 125979 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_125979 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 125979) = 177147 * m + 85133 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 125979
  rw [data_18_125979.1, data_18_125979.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_125979 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 125979) < 262144 * m + 125979 := by
  apply descent_of_endpoint
  · rw [data_18_125979.1]; exact data_18_125979.2.2
  · rw [data_18_125979.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 126183). -/
theorem data_18_126183 : oddCount 126183 18 = 11 ∧
    acceleratedOrbit 18 126183 = 85271 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_126183 : ∀ j : Fin 18,
    126183 ≤ acceleratedOrbit j.val 126183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_126183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126183) = 177147 * m + 85271 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 126183
  rw [data_18_126183.1, data_18_126183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_126183 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126183) < 262144 * m + 126183 := by
  apply descent_of_endpoint
  · rw [data_18_126183.1]; exact data_18_126183.2.2
  · rw [data_18_126183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 126623). -/
theorem data_18_126623 : oddCount 126623 18 = 11 ∧
    acceleratedOrbit 18 126623 = 85568 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_126623 : ∀ j : Fin 18,
    126623 ≤ acceleratedOrbit j.val 126623 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_126623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126623) = 177147 * m + 85568 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 126623
  rw [data_18_126623.1, data_18_126623.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_126623 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126623) < 262144 * m + 126623 := by
  apply descent_of_endpoint
  · rw [data_18_126623.1]; exact data_18_126623.2.2
  · rw [data_18_126623.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 126631). -/
theorem data_18_126631 : oddCount 126631 18 = 11 ∧
    acceleratedOrbit 18 126631 = 85574 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_126631 : ∀ j : Fin 18,
    126631 ≤ acceleratedOrbit j.val 126631 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_126631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126631) = 177147 * m + 85574 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 126631
  rw [data_18_126631.1, data_18_126631.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_126631 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126631) < 262144 * m + 126631 := by
  apply descent_of_endpoint
  · rw [data_18_126631.1]; exact data_18_126631.2.2
  · rw [data_18_126631.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 126703). -/
theorem data_18_126703 : oddCount 126703 18 = 11 ∧
    acceleratedOrbit 18 126703 = 85622 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_126703 : ∀ j : Fin 18,
    126703 ≤ acceleratedOrbit j.val 126703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_126703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126703) = 177147 * m + 85622 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 126703
  rw [data_18_126703.1, data_18_126703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_126703 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126703) < 262144 * m + 126703 := by
  apply descent_of_endpoint
  · rw [data_18_126703.1]; exact data_18_126703.2.2
  · rw [data_18_126703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 126751). -/
theorem data_18_126751 : oddCount 126751 18 = 11 ∧
    acceleratedOrbit 18 126751 = 85655 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_126751 : ∀ j : Fin 18,
    126751 ≤ acceleratedOrbit j.val 126751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_126751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126751) = 177147 * m + 85655 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 126751
  rw [data_18_126751.1, data_18_126751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_126751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 126751) < 262144 * m + 126751 := by
  apply descent_of_endpoint
  · rw [data_18_126751.1]; exact data_18_126751.2.2
  · rw [data_18_126751.2.1]; decide

end Collatz.Research.FirstDescent.Batch160
