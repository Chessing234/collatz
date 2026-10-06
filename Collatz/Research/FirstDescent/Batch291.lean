import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 291. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch291
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 214247). -/
theorem data_20_214247 : oddCount 214247 20 = 12 ∧
    acceleratedOrbit 20 214247 = 108586 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_214247 : ∀ j : Fin 20,
    214247 ≤ acceleratedOrbit j.val 214247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_214247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 214247) = 531441 * m + 108586 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 214247
  rw [data_20_214247.1, data_20_214247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_214247 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 214247) < 1048576 * m + 214247 := by
  apply descent_of_endpoint
  · rw [data_20_214247.1]; exact data_20_214247.2.2
  · rw [data_20_214247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 214503). -/
theorem data_20_214503 : oddCount 214503 20 = 12 ∧
    acceleratedOrbit 20 214503 = 108716 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_214503 : ∀ j : Fin 20,
    214503 ≤ acceleratedOrbit j.val 214503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_214503 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 214503) = 531441 * m + 108716 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 214503
  rw [data_20_214503.1, data_20_214503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_214503 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 214503) < 1048576 * m + 214503 := by
  apply descent_of_endpoint
  · rw [data_20_214503.1]; exact data_20_214503.2.2
  · rw [data_20_214503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 214575). -/
theorem data_20_214575 : oddCount 214575 20 = 12 ∧
    acceleratedOrbit 20 214575 = 108752 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_214575 : ∀ j : Fin 20,
    214575 ≤ acceleratedOrbit j.val 214575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_214575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 214575) = 531441 * m + 108752 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 214575
  rw [data_20_214575.1, data_20_214575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_214575 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 214575) < 1048576 * m + 214575 := by
  apply descent_of_endpoint
  · rw [data_20_214575.1]; exact data_20_214575.2.2
  · rw [data_20_214575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 215143). -/
theorem data_20_215143 : oddCount 215143 20 = 12 ∧
    acceleratedOrbit 20 215143 = 109040 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_215143 : ∀ j : Fin 20,
    215143 ≤ acceleratedOrbit j.val 215143 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_215143 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215143) = 531441 * m + 109040 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 215143
  rw [data_20_215143.1, data_20_215143.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_215143 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215143) < 1048576 * m + 215143 := by
  apply descent_of_endpoint
  · rw [data_20_215143.1]; exact data_20_215143.2.2
  · rw [data_20_215143.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 215295). -/
theorem data_20_215295 : oddCount 215295 20 = 12 ∧
    acceleratedOrbit 20 215295 = 109117 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_215295 : ∀ j : Fin 20,
    215295 ≤ acceleratedOrbit j.val 215295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_215295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215295) = 531441 * m + 109117 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 215295
  rw [data_20_215295.1, data_20_215295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_215295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215295) < 1048576 * m + 215295 := by
  apply descent_of_endpoint
  · rw [data_20_215295.1]; exact data_20_215295.2.2
  · rw [data_20_215295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 215711). -/
theorem data_20_215711 : oddCount 215711 20 = 12 ∧
    acceleratedOrbit 20 215711 = 109328 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_215711 : ∀ j : Fin 20,
    215711 ≤ acceleratedOrbit j.val 215711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_215711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215711) = 531441 * m + 109328 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 215711
  rw [data_20_215711.1, data_20_215711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_215711 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215711) < 1048576 * m + 215711 := by
  apply descent_of_endpoint
  · rw [data_20_215711.1]; exact data_20_215711.2.2
  · rw [data_20_215711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 215871). -/
theorem data_20_215871 : oddCount 215871 20 = 12 ∧
    acceleratedOrbit 20 215871 = 109409 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_215871 : ∀ j : Fin 20,
    215871 ≤ acceleratedOrbit j.val 215871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_215871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215871) = 531441 * m + 109409 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 215871
  rw [data_20_215871.1, data_20_215871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_215871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 215871) < 1048576 * m + 215871 := by
  apply descent_of_endpoint
  · rw [data_20_215871.1]; exact data_20_215871.2.2
  · rw [data_20_215871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 216271). -/
theorem data_20_216271 : oddCount 216271 20 = 12 ∧
    acceleratedOrbit 20 216271 = 109612 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_216271 : ∀ j : Fin 20,
    216271 ≤ acceleratedOrbit j.val 216271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_216271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216271) = 531441 * m + 109612 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 216271
  rw [data_20_216271.1, data_20_216271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_216271 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 216271) < 1048576 * m + 216271 := by
  apply descent_of_endpoint
  · rw [data_20_216271.1]; exact data_20_216271.2.2
  · rw [data_20_216271.2.1]; decide

end Collatz.Research.FirstDescent.Batch291
