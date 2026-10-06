import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 40. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch040
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (15, 32603). -/
theorem data_15_32603 : oddCount 32603 15 = 9 ∧
    acceleratedOrbit 15 32603 = 19585 ∧ 19683 < 32768 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_15_32603 : ∀ j : Fin 15,
    32603 ≤ acceleratedOrbit j.val 32603 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_15_32603 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32603) = 19683 * m + 19585 := by
  have h := Congruence.accOrbit_pow_two_mul_add 15 m 32603
  rw [data_15_32603.1, data_15_32603.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_15_32603 (m : Nat) :
    acceleratedOrbit 15 (32768 * m + 32603) < 32768 * m + 32603 := by
  apply descent_of_endpoint
  · rw [data_15_32603.1]; exact data_15_32603.2.2
  · rw [data_15_32603.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 359). -/
theorem data_16_359 : oddCount 359 16 = 10 ∧
    acceleratedOrbit 16 359 = 325 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_359 : ∀ j : Fin 16,
    359 ≤ acceleratedOrbit j.val 359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 359) = 59049 * m + 325 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 359
  rw [data_16_359.1, data_16_359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_359 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 359) < 65536 * m + 359 := by
  apply descent_of_endpoint
  · rw [data_16_359.1]; exact data_16_359.2.2
  · rw [data_16_359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 479). -/
theorem data_16_479 : oddCount 479 16 = 10 ∧
    acceleratedOrbit 16 479 = 433 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_479 : ∀ j : Fin 16,
    479 ≤ acceleratedOrbit j.val 479 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_479 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 479) = 59049 * m + 433 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 479
  rw [data_16_479.1, data_16_479.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_479 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 479) < 65536 * m + 479 := by
  apply descent_of_endpoint
  · rw [data_16_479.1]; exact data_16_479.2.2
  · rw [data_16_479.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 559). -/
theorem data_16_559 : oddCount 559 16 = 10 ∧
    acceleratedOrbit 16 559 = 505 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_559 : ∀ j : Fin 16,
    559 ≤ acceleratedOrbit j.val 559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 559) = 59049 * m + 505 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 559
  rw [data_16_559.1, data_16_559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_559 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 559) < 65536 * m + 559 := by
  apply descent_of_endpoint
  · rw [data_16_559.1]; exact data_16_559.2.2
  · rw [data_16_559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 603). -/
theorem data_16_603 : oddCount 603 16 = 10 ∧
    acceleratedOrbit 16 603 = 545 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_603 : ∀ j : Fin 16,
    603 ≤ acceleratedOrbit j.val 603 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_603 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 603) = 59049 * m + 545 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 603
  rw [data_16_603.1, data_16_603.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_603 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 603) < 65536 * m + 603 := by
  apply descent_of_endpoint
  · rw [data_16_603.1]; exact data_16_603.2.2
  · rw [data_16_603.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 767). -/
theorem data_16_767 : oddCount 767 16 = 10 ∧
    acceleratedOrbit 16 767 = 692 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_767 : ∀ j : Fin 16,
    767 ≤ acceleratedOrbit j.val 767 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_767 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 767) = 59049 * m + 692 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 767
  rw [data_16_767.1, data_16_767.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_767 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 767) < 65536 * m + 767 := by
  apply descent_of_endpoint
  · rw [data_16_767.1]; exact data_16_767.2.2
  · rw [data_16_767.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 859). -/
theorem data_16_859 : oddCount 859 16 = 10 ∧
    acceleratedOrbit 16 859 = 776 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_859 : ∀ j : Fin 16,
    859 ≤ acceleratedOrbit j.val 859 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_859 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 859) = 59049 * m + 776 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 859
  rw [data_16_859.1, data_16_859.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_859 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 859) < 65536 * m + 859 := by
  apply descent_of_endpoint
  · rw [data_16_859.1]; exact data_16_859.2.2
  · rw [data_16_859.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 1179). -/
theorem data_16_1179 : oddCount 1179 16 = 10 ∧
    acceleratedOrbit 16 1179 = 1064 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_1179 : ∀ j : Fin 16,
    1179 ≤ acceleratedOrbit j.val 1179 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_1179 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1179) = 59049 * m + 1064 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 1179
  rw [data_16_1179.1, data_16_1179.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_1179 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 1179) < 65536 * m + 1179 := by
  apply descent_of_endpoint
  · rw [data_16_1179.1]; exact data_16_1179.2.2
  · rw [data_16_1179.2.1]; decide

end Collatz.Research.FirstDescent.Batch040
