import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 63. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch063
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26015). -/
theorem data_16_26015 : oddCount 26015 16 = 10 ∧
    acceleratedOrbit 16 26015 = 23441 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26015 : ∀ j : Fin 16,
    26015 ≤ acceleratedOrbit j.val 26015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26015) = 59049 * m + 23441 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26015
  rw [data_16_26015.1, data_16_26015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26015 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26015) < 65536 * m + 26015 := by
  apply descent_of_endpoint
  · rw [data_16_26015.1]; exact data_16_26015.2.2
  · rw [data_16_26015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26063). -/
theorem data_16_26063 : oddCount 26063 16 = 10 ∧
    acceleratedOrbit 16 26063 = 23485 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26063 : ∀ j : Fin 16,
    26063 ≤ acceleratedOrbit j.val 26063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26063 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26063) = 59049 * m + 23485 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26063
  rw [data_16_26063.1, data_16_26063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26063 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26063) < 65536 * m + 26063 := by
  apply descent_of_endpoint
  · rw [data_16_26063.1]; exact data_16_26063.2.2
  · rw [data_16_26063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26343). -/
theorem data_16_26343 : oddCount 26343 16 = 10 ∧
    acceleratedOrbit 16 26343 = 23737 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26343 : ∀ j : Fin 16,
    26343 ≤ acceleratedOrbit j.val 26343 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26343) = 59049 * m + 23737 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26343
  rw [data_16_26343.1, data_16_26343.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26343 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26343) < 65536 * m + 26343 := by
  apply descent_of_endpoint
  · rw [data_16_26343.1]; exact data_16_26343.2.2
  · rw [data_16_26343.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26351). -/
theorem data_16_26351 : oddCount 26351 16 = 10 ∧
    acceleratedOrbit 16 26351 = 23744 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26351 : ∀ j : Fin 16,
    26351 ≤ acceleratedOrbit j.val 26351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26351) = 59049 * m + 23744 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26351
  rw [data_16_26351.1, data_16_26351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26351 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26351) < 65536 * m + 26351 := by
  apply descent_of_endpoint
  · rw [data_16_26351.1]; exact data_16_26351.2.2
  · rw [data_16_26351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26367). -/
theorem data_16_26367 : oddCount 26367 16 = 10 ∧
    acceleratedOrbit 16 26367 = 23758 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26367 : ∀ j : Fin 16,
    26367 ≤ acceleratedOrbit j.val 26367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26367 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26367) = 59049 * m + 23758 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26367
  rw [data_16_26367.1, data_16_26367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26367 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26367) < 65536 * m + 26367 := by
  apply descent_of_endpoint
  · rw [data_16_26367.1]; exact data_16_26367.2.2
  · rw [data_16_26367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26439). -/
theorem data_16_26439 : oddCount 26439 16 = 10 ∧
    acceleratedOrbit 16 26439 = 23824 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26439 : ∀ j : Fin 16,
    26439 ≤ acceleratedOrbit j.val 26439 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26439) = 59049 * m + 23824 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26439
  rw [data_16_26439.1, data_16_26439.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26439 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26439) < 65536 * m + 26439 := by
  apply descent_of_endpoint
  · rw [data_16_26439.1]; exact data_16_26439.2.2
  · rw [data_16_26439.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26459). -/
theorem data_16_26459 : oddCount 26459 16 = 10 ∧
    acceleratedOrbit 16 26459 = 23842 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26459 : ∀ j : Fin 16,
    26459 ≤ acceleratedOrbit j.val 26459 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26459 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26459) = 59049 * m + 23842 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26459
  rw [data_16_26459.1, data_16_26459.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26459 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26459) < 65536 * m + 26459 := by
  apply descent_of_endpoint
  · rw [data_16_26459.1]; exact data_16_26459.2.2
  · rw [data_16_26459.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 26619). -/
theorem data_16_26619 : oddCount 26619 16 = 10 ∧
    acceleratedOrbit 16 26619 = 23986 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_26619 : ∀ j : Fin 16,
    26619 ≤ acceleratedOrbit j.val 26619 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_26619 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26619) = 59049 * m + 23986 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 26619
  rw [data_16_26619.1, data_16_26619.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_26619 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 26619) < 65536 * m + 26619 := by
  apply descent_of_endpoint
  · rw [data_16_26619.1]; exact data_16_26619.2.2
  · rw [data_16_26619.2.1]; decide

end Collatz.Research.FirstDescent.Batch063
