import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 269. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch269
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 147303). -/
theorem data_20_147303 : oddCount 147303 20 = 12 ∧
    acceleratedOrbit 20 147303 = 74657 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_147303 : ∀ j : Fin 20,
    147303 ≤ acceleratedOrbit j.val 147303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_147303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 147303) = 531441 * m + 74657 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 147303
  rw [data_20_147303.1, data_20_147303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_147303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 147303) < 1048576 * m + 147303 := by
  apply descent_of_endpoint
  · rw [data_20_147303.1]; exact data_20_147303.2.2
  · rw [data_20_147303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 148327). -/
theorem data_20_148327 : oddCount 148327 20 = 12 ∧
    acceleratedOrbit 20 148327 = 75176 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_148327 : ∀ j : Fin 20,
    148327 ≤ acceleratedOrbit j.val 148327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_148327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 148327) = 531441 * m + 75176 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 148327
  rw [data_20_148327.1, data_20_148327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_148327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 148327) < 1048576 * m + 148327 := by
  apply descent_of_endpoint
  · rw [data_20_148327.1]; exact data_20_148327.2.2
  · rw [data_20_148327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 148711). -/
theorem data_20_148711 : oddCount 148711 20 = 12 ∧
    acceleratedOrbit 20 148711 = 75371 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_148711 : ∀ j : Fin 20,
    148711 ≤ acceleratedOrbit j.val 148711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_148711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 148711) = 531441 * m + 75371 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 148711
  rw [data_20_148711.1, data_20_148711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_148711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 148711) < 1048576 * m + 148711 := by
  apply descent_of_endpoint
  · rw [data_20_148711.1]; exact data_20_148711.2.2
  · rw [data_20_148711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 149147). -/
theorem data_20_149147 : oddCount 149147 20 = 12 ∧
    acceleratedOrbit 20 149147 = 75592 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_149147 : ∀ j : Fin 20,
    149147 ≤ acceleratedOrbit j.val 149147 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_149147 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149147) = 531441 * m + 75592 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 149147
  rw [data_20_149147.1, data_20_149147.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_149147 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149147) < 1048576 * m + 149147 := by
  apply descent_of_endpoint
  · rw [data_20_149147.1]; exact data_20_149147.2.2
  · rw [data_20_149147.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 149351). -/
theorem data_20_149351 : oddCount 149351 20 = 12 ∧
    acceleratedOrbit 20 149351 = 75695 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_149351 : ∀ j : Fin 20,
    149351 ≤ acceleratedOrbit j.val 149351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_149351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149351) = 531441 * m + 75695 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 149351
  rw [data_20_149351.1, data_20_149351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_149351 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149351) < 1048576 * m + 149351 := by
  apply descent_of_endpoint
  · rw [data_20_149351.1]; exact data_20_149351.2.2
  · rw [data_20_149351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 149759). -/
theorem data_20_149759 : oddCount 149759 20 = 12 ∧
    acceleratedOrbit 20 149759 = 75902 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_149759 : ∀ j : Fin 20,
    149759 ≤ acceleratedOrbit j.val 149759 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_149759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149759) = 531441 * m + 75902 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 149759
  rw [data_20_149759.1, data_20_149759.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_149759 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149759) < 1048576 * m + 149759 := by
  apply descent_of_endpoint
  · rw [data_20_149759.1]; exact data_20_149759.2.2
  · rw [data_20_149759.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 149919). -/
theorem data_20_149919 : oddCount 149919 20 = 12 ∧
    acceleratedOrbit 20 149919 = 75983 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_149919 : ∀ j : Fin 20,
    149919 ≤ acceleratedOrbit j.val 149919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_149919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149919) = 531441 * m + 75983 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 149919
  rw [data_20_149919.1, data_20_149919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_149919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 149919) < 1048576 * m + 149919 := by
  apply descent_of_endpoint
  · rw [data_20_149919.1]; exact data_20_149919.2.2
  · rw [data_20_149919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 150511). -/
theorem data_20_150511 : oddCount 150511 20 = 12 ∧
    acceleratedOrbit 20 150511 = 76283 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_150511 : ∀ j : Fin 20,
    150511 ≤ acceleratedOrbit j.val 150511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_150511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150511) = 531441 * m + 76283 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 150511
  rw [data_20_150511.1, data_20_150511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_150511 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 150511) < 1048576 * m + 150511 := by
  apply descent_of_endpoint
  · rw [data_20_150511.1]; exact data_20_150511.2.2
  · rw [data_20_150511.2.1]; decide

end Collatz.Research.FirstDescent.Batch269
