import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 134. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch134
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70175). -/
theorem data_18_70175 : oddCount 70175 18 = 11 ∧
    acceleratedOrbit 18 70175 = 47423 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70175 : ∀ j : Fin 18,
    70175 ≤ acceleratedOrbit j.val 70175 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70175) = 177147 * m + 47423 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70175
  rw [data_18_70175.1, data_18_70175.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70175 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70175) < 262144 * m + 70175 := by
  apply descent_of_endpoint
  · rw [data_18_70175.1]; exact data_18_70175.2.2
  · rw [data_18_70175.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70255). -/
theorem data_18_70255 : oddCount 70255 18 = 11 ∧
    acceleratedOrbit 18 70255 = 47477 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70255 : ∀ j : Fin 18,
    70255 ≤ acceleratedOrbit j.val 70255 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70255) = 177147 * m + 47477 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70255
  rw [data_18_70255.1, data_18_70255.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70255 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70255) < 262144 * m + 70255 := by
  apply descent_of_endpoint
  · rw [data_18_70255.1]; exact data_18_70255.2.2
  · rw [data_18_70255.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70303). -/
theorem data_18_70303 : oddCount 70303 18 = 11 ∧
    acceleratedOrbit 18 70303 = 47509 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70303 : ∀ j : Fin 18,
    70303 ≤ acceleratedOrbit j.val 70303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70303 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70303) = 177147 * m + 47509 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70303
  rw [data_18_70303.1, data_18_70303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70303 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70303) < 262144 * m + 70303 := by
  apply descent_of_endpoint
  · rw [data_18_70303.1]; exact data_18_70303.2.2
  · rw [data_18_70303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70375). -/
theorem data_18_70375 : oddCount 70375 18 = 11 ∧
    acceleratedOrbit 18 70375 = 47558 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70375 : ∀ j : Fin 18,
    70375 ≤ acceleratedOrbit j.val 70375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70375) = 177147 * m + 47558 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70375
  rw [data_18_70375.1, data_18_70375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70375 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70375) < 262144 * m + 70375 := by
  apply descent_of_endpoint
  · rw [data_18_70375.1]; exact data_18_70375.2.2
  · rw [data_18_70375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70383). -/
theorem data_18_70383 : oddCount 70383 18 = 11 ∧
    acceleratedOrbit 18 70383 = 47563 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70383 : ∀ j : Fin 18,
    70383 ≤ acceleratedOrbit j.val 70383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70383 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70383) = 177147 * m + 47563 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70383
  rw [data_18_70383.1, data_18_70383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70383 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70383) < 262144 * m + 70383 := by
  apply descent_of_endpoint
  · rw [data_18_70383.1]; exact data_18_70383.2.2
  · rw [data_18_70383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70427). -/
theorem data_18_70427 : oddCount 70427 18 = 11 ∧
    acceleratedOrbit 18 70427 = 47593 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70427 : ∀ j : Fin 18,
    70427 ≤ acceleratedOrbit j.val 70427 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70427 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70427) = 177147 * m + 47593 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70427
  rw [data_18_70427.1, data_18_70427.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70427 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70427) < 262144 * m + 70427 := by
  apply descent_of_endpoint
  · rw [data_18_70427.1]; exact data_18_70427.2.2
  · rw [data_18_70427.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70815). -/
theorem data_18_70815 : oddCount 70815 18 = 11 ∧
    acceleratedOrbit 18 70815 = 47855 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70815 : ∀ j : Fin 18,
    70815 ≤ acceleratedOrbit j.val 70815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70815 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70815) = 177147 * m + 47855 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70815
  rw [data_18_70815.1, data_18_70815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70815 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70815) < 262144 * m + 70815 := by
  apply descent_of_endpoint
  · rw [data_18_70815.1]; exact data_18_70815.2.2
  · rw [data_18_70815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 70939). -/
theorem data_18_70939 : oddCount 70939 18 = 11 ∧
    acceleratedOrbit 18 70939 = 47939 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_70939 : ∀ j : Fin 18,
    70939 ≤ acceleratedOrbit j.val 70939 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_70939 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70939) = 177147 * m + 47939 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 70939
  rw [data_18_70939.1, data_18_70939.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_70939 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 70939) < 262144 * m + 70939 := by
  apply descent_of_endpoint
  · rw [data_18_70939.1]; exact data_18_70939.2.2
  · rw [data_18_70939.2.1]; decide

end Collatz.Research.FirstDescent.Batch134
