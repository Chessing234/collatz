import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 211. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch211
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 243327). -/
theorem data_18_243327 : oddCount 243327 18 = 11 ∧
    acceleratedOrbit 18 243327 = 164432 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_243327 : ∀ j : Fin 18,
    243327 ≤ acceleratedOrbit j.val 243327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_243327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 243327) = 177147 * m + 164432 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 243327
  rw [data_18_243327.1, data_18_243327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_243327 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 243327) < 262144 * m + 243327 := by
  apply descent_of_endpoint
  · rw [data_18_243327.1]; exact data_18_243327.2.2
  · rw [data_18_243327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 243739). -/
theorem data_18_243739 : oddCount 243739 18 = 11 ∧
    acceleratedOrbit 18 243739 = 164711 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_243739 : ∀ j : Fin 18,
    243739 ≤ acceleratedOrbit j.val 243739 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_243739 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 243739) = 177147 * m + 164711 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 243739
  rw [data_18_243739.1, data_18_243739.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_243739 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 243739) < 262144 * m + 243739 := by
  apply descent_of_endpoint
  · rw [data_18_243739.1]; exact data_18_243739.2.2
  · rw [data_18_243739.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 244071). -/
theorem data_18_244071 : oddCount 244071 18 = 11 ∧
    acceleratedOrbit 18 244071 = 164935 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_244071 : ∀ j : Fin 18,
    244071 ≤ acceleratedOrbit j.val 244071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_244071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244071) = 177147 * m + 164935 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 244071
  rw [data_18_244071.1, data_18_244071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_244071 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244071) < 262144 * m + 244071 := by
  apply descent_of_endpoint
  · rw [data_18_244071.1]; exact data_18_244071.2.2
  · rw [data_18_244071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 244191). -/
theorem data_18_244191 : oddCount 244191 18 = 11 ∧
    acceleratedOrbit 18 244191 = 165016 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_244191 : ∀ j : Fin 18,
    244191 ≤ acceleratedOrbit j.val 244191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_244191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244191) = 177147 * m + 165016 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 244191
  rw [data_18_244191.1, data_18_244191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_244191 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244191) < 262144 * m + 244191 := by
  apply descent_of_endpoint
  · rw [data_18_244191.1]; exact data_18_244191.2.2
  · rw [data_18_244191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 244351). -/
theorem data_18_244351 : oddCount 244351 18 = 11 ∧
    acceleratedOrbit 18 244351 = 165124 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_244351 : ∀ j : Fin 18,
    244351 ≤ acceleratedOrbit j.val 244351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_244351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244351) = 177147 * m + 165124 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 244351
  rw [data_18_244351.1, data_18_244351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_244351 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244351) < 262144 * m + 244351 := by
  apply descent_of_endpoint
  · rw [data_18_244351.1]; exact data_18_244351.2.2
  · rw [data_18_244351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 244543). -/
theorem data_18_244543 : oddCount 244543 18 = 11 ∧
    acceleratedOrbit 18 244543 = 165254 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_244543 : ∀ j : Fin 18,
    244543 ≤ acceleratedOrbit j.val 244543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_244543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244543) = 177147 * m + 165254 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 244543
  rw [data_18_244543.1, data_18_244543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_244543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244543) < 262144 * m + 244543 := by
  apply descent_of_endpoint
  · rw [data_18_244543.1]; exact data_18_244543.2.2
  · rw [data_18_244543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 244583). -/
theorem data_18_244583 : oddCount 244583 18 = 11 ∧
    acceleratedOrbit 18 244583 = 165281 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_244583 : ∀ j : Fin 18,
    244583 ≤ acceleratedOrbit j.val 244583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_244583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244583) = 177147 * m + 165281 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 244583
  rw [data_18_244583.1, data_18_244583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_244583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244583) < 262144 * m + 244583 := by
  apply descent_of_endpoint
  · rw [data_18_244583.1]; exact data_18_244583.2.2
  · rw [data_18_244583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 244863). -/
theorem data_18_244863 : oddCount 244863 18 = 11 ∧
    acceleratedOrbit 18 244863 = 165470 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_244863 : ∀ j : Fin 18,
    244863 ≤ acceleratedOrbit j.val 244863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_244863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244863) = 177147 * m + 165470 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 244863
  rw [data_18_244863.1, data_18_244863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_244863 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 244863) < 262144 * m + 244863 := by
  apply descent_of_endpoint
  · rw [data_18_244863.1]; exact data_18_244863.2.2
  · rw [data_18_244863.2.1]; decide

end Collatz.Research.FirstDescent.Batch211
