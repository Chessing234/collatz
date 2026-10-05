import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 56. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch056
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17479). -/
theorem data_16_17479 : oddCount 17479 16 = 10 ∧
    acceleratedOrbit 16 17479 = 15751 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17479 : ∀ j : Fin 16,
    17479 ≤ acceleratedOrbit j.val 17479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17479 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17479) = 59049 * m + 15751 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17479
  rw [data_16_17479.1, data_16_17479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17479 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17479) < 65536 * m + 17479 := by
  apply descent_of_endpoint
  · rw [data_16_17479.1]; exact data_16_17479.2.2
  · rw [data_16_17479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17511). -/
theorem data_16_17511 : oddCount 17511 16 = 10 ∧
    acceleratedOrbit 16 17511 = 15779 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17511 : ∀ j : Fin 16,
    17511 ≤ acceleratedOrbit j.val 17511 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17511 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17511) = 59049 * m + 15779 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17511
  rw [data_16_17511.1, data_16_17511.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17511 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17511) < 65536 * m + 17511 := by
  apply descent_of_endpoint
  · rw [data_16_17511.1]; exact data_16_17511.2.2
  · rw [data_16_17511.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 17659). -/
theorem data_16_17659 : oddCount 17659 16 = 10 ∧
    acceleratedOrbit 16 17659 = 15913 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_17659 : ∀ j : Fin 16,
    17659 ≤ acceleratedOrbit j.val 17659 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_17659 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17659) = 59049 * m + 15913 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 17659
  rw [data_16_17659.1, data_16_17659.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_17659 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 17659) < 65536 * m + 17659 := by
  apply descent_of_endpoint
  · rw [data_16_17659.1]; exact data_16_17659.2.2
  · rw [data_16_17659.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 18159). -/
theorem data_16_18159 : oddCount 18159 16 = 10 ∧
    acceleratedOrbit 16 18159 = 16363 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_18159 : ∀ j : Fin 16,
    18159 ≤ acceleratedOrbit j.val 18159 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_18159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18159) = 59049 * m + 16363 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 18159
  rw [data_16_18159.1, data_16_18159.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_18159 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18159) < 65536 * m + 18159 := by
  apply descent_of_endpoint
  · rw [data_16_18159.1]; exact data_16_18159.2.2
  · rw [data_16_18159.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 18343). -/
theorem data_16_18343 : oddCount 18343 16 = 10 ∧
    acceleratedOrbit 16 18343 = 16529 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_18343 : ∀ j : Fin 16,
    18343 ≤ acceleratedOrbit j.val 18343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_18343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18343) = 59049 * m + 16529 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 18343
  rw [data_16_18343.1, data_16_18343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_18343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18343) < 65536 * m + 18343 := by
  apply descent_of_endpoint
  · rw [data_16_18343.1]; exact data_16_18343.2.2
  · rw [data_16_18343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 18523). -/
theorem data_16_18523 : oddCount 18523 16 = 10 ∧
    acceleratedOrbit 16 18523 = 16691 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_18523 : ∀ j : Fin 16,
    18523 ≤ acceleratedOrbit j.val 18523 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_18523 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18523) = 59049 * m + 16691 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 18523
  rw [data_16_18523.1, data_16_18523.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_18523 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18523) < 65536 * m + 18523 := by
  apply descent_of_endpoint
  · rw [data_16_18523.1]; exact data_16_18523.2.2
  · rw [data_16_18523.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 18559). -/
theorem data_16_18559 : oddCount 18559 16 = 10 ∧
    acceleratedOrbit 16 18559 = 16723 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_18559 : ∀ j : Fin 16,
    18559 ≤ acceleratedOrbit j.val 18559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_18559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18559) = 59049 * m + 16723 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 18559
  rw [data_16_18559.1, data_16_18559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_18559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18559) < 65536 * m + 18559 := by
  apply descent_of_endpoint
  · rw [data_16_18559.1]; exact data_16_18559.2.2
  · rw [data_16_18559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 18919). -/
theorem data_16_18919 : oddCount 18919 16 = 10 ∧
    acceleratedOrbit 16 18919 = 17048 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_18919 : ∀ j : Fin 16,
    18919 ≤ acceleratedOrbit j.val 18919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_18919 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18919) = 59049 * m + 17048 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 18919
  rw [data_16_18919.1, data_16_18919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_18919 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 18919) < 65536 * m + 18919 := by
  apply descent_of_endpoint
  · rw [data_16_18919.1]; exact data_16_18919.2.2
  · rw [data_16_18919.2.1]; decide

end Collatz.Research.FirstDescent.Batch056
