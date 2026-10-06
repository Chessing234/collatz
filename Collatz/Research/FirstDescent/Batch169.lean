import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 169. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch169
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148123). -/
theorem data_18_148123 : oddCount 148123 18 = 11 ∧
    acceleratedOrbit 18 148123 = 100097 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148123 : ∀ j : Fin 18,
    148123 ≤ acceleratedOrbit j.val 148123 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148123 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148123) = 177147 * m + 100097 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148123
  rw [data_18_148123.1, data_18_148123.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148123 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148123) < 262144 * m + 148123 := by
  apply descent_of_endpoint
  · rw [data_18_148123.1]; exact data_18_148123.2.2
  · rw [data_18_148123.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148287). -/
theorem data_18_148287 : oddCount 148287 18 = 11 ∧
    acceleratedOrbit 18 148287 = 100208 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148287 : ∀ j : Fin 18,
    148287 ≤ acceleratedOrbit j.val 148287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148287) = 177147 * m + 100208 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148287
  rw [data_18_148287.1, data_18_148287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148287) < 262144 * m + 148287 := by
  apply descent_of_endpoint
  · rw [data_18_148287.1]; exact data_18_148287.2.2
  · rw [data_18_148287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148415). -/
theorem data_18_148415 : oddCount 148415 18 = 11 ∧
    acceleratedOrbit 18 148415 = 100294 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148415 : ∀ j : Fin 18,
    148415 ≤ acceleratedOrbit j.val 148415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148415) = 177147 * m + 100294 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148415
  rw [data_18_148415.1, data_18_148415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148415 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148415) < 262144 * m + 148415 := by
  apply descent_of_endpoint
  · rw [data_18_148415.1]; exact data_18_148415.2.2
  · rw [data_18_148415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148447). -/
theorem data_18_148447 : oddCount 148447 18 = 11 ∧
    acceleratedOrbit 18 148447 = 100316 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148447 : ∀ j : Fin 18,
    148447 ≤ acceleratedOrbit j.val 148447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148447) = 177147 * m + 100316 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148447
  rw [data_18_148447.1, data_18_148447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148447) < 262144 * m + 148447 := by
  apply descent_of_endpoint
  · rw [data_18_148447.1]; exact data_18_148447.2.2
  · rw [data_18_148447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148571). -/
theorem data_18_148571 : oddCount 148571 18 = 11 ∧
    acceleratedOrbit 18 148571 = 100400 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148571 : ∀ j : Fin 18,
    148571 ≤ acceleratedOrbit j.val 148571 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148571 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148571) = 177147 * m + 100400 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148571
  rw [data_18_148571.1, data_18_148571.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148571 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148571) < 262144 * m + 148571 := by
  apply descent_of_endpoint
  · rw [data_18_148571.1]; exact data_18_148571.2.2
  · rw [data_18_148571.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 148607). -/
theorem data_18_148607 : oddCount 148607 18 = 11 ∧
    acceleratedOrbit 18 148607 = 100424 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_148607 : ∀ j : Fin 18,
    148607 ≤ acceleratedOrbit j.val 148607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_148607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148607) = 177147 * m + 100424 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 148607
  rw [data_18_148607.1, data_18_148607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_148607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 148607) < 262144 * m + 148607 := by
  apply descent_of_endpoint
  · rw [data_18_148607.1]; exact data_18_148607.2.2
  · rw [data_18_148607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 149951). -/
theorem data_18_149951 : oddCount 149951 18 = 11 ∧
    acceleratedOrbit 18 149951 = 101332 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_149951 : ∀ j : Fin 18,
    149951 ≤ acceleratedOrbit j.val 149951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_149951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 149951) = 177147 * m + 101332 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 149951
  rw [data_18_149951.1, data_18_149951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_149951 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 149951) < 262144 * m + 149951 := by
  apply descent_of_endpoint
  · rw [data_18_149951.1]; exact data_18_149951.2.2
  · rw [data_18_149951.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 150463). -/
theorem data_18_150463 : oddCount 150463 18 = 11 ∧
    acceleratedOrbit 18 150463 = 101678 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_150463 : ∀ j : Fin 18,
    150463 ≤ acceleratedOrbit j.val 150463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_150463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 150463) = 177147 * m + 101678 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 150463
  rw [data_18_150463.1, data_18_150463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_150463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 150463) < 262144 * m + 150463 := by
  apply descent_of_endpoint
  · rw [data_18_150463.1]; exact data_18_150463.2.2
  · rw [data_18_150463.2.1]; decide

end Collatz.Research.FirstDescent.Batch169
