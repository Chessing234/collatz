import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 290. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch290
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 208967). -/
theorem data_20_208967 : oddCount 208967 20 = 12 ∧
    acceleratedOrbit 20 208967 = 105910 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_208967 : ∀ j : Fin 20,
    208967 ≤ acceleratedOrbit j.val 208967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_208967 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 208967) = 531441 * m + 105910 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 208967
  rw [data_20_208967.1, data_20_208967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_208967 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 208967) < 1048576 * m + 208967 := by
  apply descent_of_endpoint
  · rw [data_20_208967.1]; exact data_20_208967.2.2
  · rw [data_20_208967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 209691). -/
theorem data_20_209691 : oddCount 209691 20 = 12 ∧
    acceleratedOrbit 20 209691 = 106277 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_209691 : ∀ j : Fin 20,
    209691 ≤ acceleratedOrbit j.val 209691 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_209691 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 209691) = 531441 * m + 106277 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 209691
  rw [data_20_209691.1, data_20_209691.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_209691 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 209691) < 1048576 * m + 209691 := by
  apply descent_of_endpoint
  · rw [data_20_209691.1]; exact data_20_209691.2.2
  · rw [data_20_209691.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 209967). -/
theorem data_20_209967 : oddCount 209967 20 = 12 ∧
    acceleratedOrbit 20 209967 = 106417 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_209967 : ∀ j : Fin 20,
    209967 ≤ acceleratedOrbit j.val 209967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_209967 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 209967) = 531441 * m + 106417 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 209967
  rw [data_20_209967.1, data_20_209967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_209967 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 209967) < 1048576 * m + 209967 := by
  apply descent_of_endpoint
  · rw [data_20_209967.1]; exact data_20_209967.2.2
  · rw [data_20_209967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 210047). -/
theorem data_20_210047 : oddCount 210047 20 = 12 ∧
    acceleratedOrbit 20 210047 = 106457 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_210047 : ∀ j : Fin 20,
    210047 ≤ acceleratedOrbit j.val 210047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_210047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 210047) = 531441 * m + 106457 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 210047
  rw [data_20_210047.1, data_20_210047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_210047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 210047) < 1048576 * m + 210047 := by
  apply descent_of_endpoint
  · rw [data_20_210047.1]; exact data_20_210047.2.2
  · rw [data_20_210047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 210335). -/
theorem data_20_210335 : oddCount 210335 20 = 12 ∧
    acceleratedOrbit 20 210335 = 106603 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_210335 : ∀ j : Fin 20,
    210335 ≤ acceleratedOrbit j.val 210335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_210335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 210335) = 531441 * m + 106603 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 210335
  rw [data_20_210335.1, data_20_210335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_210335 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 210335) < 1048576 * m + 210335 := by
  apply descent_of_endpoint
  · rw [data_20_210335.1]; exact data_20_210335.2.2
  · rw [data_20_210335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 212071). -/
theorem data_20_212071 : oddCount 212071 20 = 12 ∧
    acceleratedOrbit 20 212071 = 107483 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_212071 : ∀ j : Fin 20,
    212071 ≤ acceleratedOrbit j.val 212071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_212071 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 212071) = 531441 * m + 107483 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 212071
  rw [data_20_212071.1, data_20_212071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_212071 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 212071) < 1048576 * m + 212071 := by
  apply descent_of_endpoint
  · rw [data_20_212071.1]; exact data_20_212071.2.2
  · rw [data_20_212071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 212383). -/
theorem data_20_212383 : oddCount 212383 20 = 12 ∧
    acceleratedOrbit 20 212383 = 107641 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_212383 : ∀ j : Fin 20,
    212383 ≤ acceleratedOrbit j.val 212383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_212383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 212383) = 531441 * m + 107641 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 212383
  rw [data_20_212383.1, data_20_212383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_212383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 212383) < 1048576 * m + 212383 := by
  apply descent_of_endpoint
  · rw [data_20_212383.1]; exact data_20_212383.2.2
  · rw [data_20_212383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 213083). -/
theorem data_20_213083 : oddCount 213083 20 = 12 ∧
    acceleratedOrbit 20 213083 = 107996 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_213083 : ∀ j : Fin 20,
    213083 ≤ acceleratedOrbit j.val 213083 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_213083 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 213083) = 531441 * m + 107996 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 213083
  rw [data_20_213083.1, data_20_213083.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_213083 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 213083) < 1048576 * m + 213083 := by
  apply descent_of_endpoint
  · rw [data_20_213083.1]; exact data_20_213083.2.2
  · rw [data_20_213083.2.1]; decide

end Collatz.Research.FirstDescent.Batch290
