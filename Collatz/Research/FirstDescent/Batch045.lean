import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 45. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch045
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5583). -/
theorem data_16_5583 : oddCount 5583 16 = 10 ∧
    acceleratedOrbit 16 5583 = 5032 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5583 : ∀ j : Fin 16,
    5583 ≤ acceleratedOrbit j.val 5583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5583 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5583) = 59049 * m + 5032 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5583
  rw [data_16_5583.1, data_16_5583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5583 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5583) < 65536 * m + 5583 := by
  apply descent_of_endpoint
  · rw [data_16_5583.1]; exact data_16_5583.2.2
  · rw [data_16_5583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5663). -/
theorem data_16_5663 : oddCount 5663 16 = 10 ∧
    acceleratedOrbit 16 5663 = 5104 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5663 : ∀ j : Fin 16,
    5663 ≤ acceleratedOrbit j.val 5663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5663) = 59049 * m + 5104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5663
  rw [data_16_5663.1, data_16_5663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5663 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5663) < 65536 * m + 5663 := by
  apply descent_of_endpoint
  · rw [data_16_5663.1]; exact data_16_5663.2.2
  · rw [data_16_5663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5823). -/
theorem data_16_5823 : oddCount 5823 16 = 10 ∧
    acceleratedOrbit 16 5823 = 5248 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5823 : ∀ j : Fin 16,
    5823 ≤ acceleratedOrbit j.val 5823 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5823 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5823) = 59049 * m + 5248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5823
  rw [data_16_5823.1, data_16_5823.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5823 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5823) < 65536 * m + 5823 := by
  apply descent_of_endpoint
  · rw [data_16_5823.1]; exact data_16_5823.2.2
  · rw [data_16_5823.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 5863). -/
theorem data_16_5863 : oddCount 5863 16 = 10 ∧
    acceleratedOrbit 16 5863 = 5284 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_5863 : ∀ j : Fin 16,
    5863 ≤ acceleratedOrbit j.val 5863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_5863 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5863) = 59049 * m + 5284 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 5863
  rw [data_16_5863.1, data_16_5863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_5863 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 5863) < 65536 * m + 5863 := by
  apply descent_of_endpoint
  · rw [data_16_5863.1]; exact data_16_5863.2.2
  · rw [data_16_5863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 6207). -/
theorem data_16_6207 : oddCount 6207 16 = 10 ∧
    acceleratedOrbit 16 6207 = 5594 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_6207 : ∀ j : Fin 16,
    6207 ≤ acceleratedOrbit j.val 6207 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_6207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6207) = 59049 * m + 5594 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 6207
  rw [data_16_6207.1, data_16_6207.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_6207 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6207) < 65536 * m + 6207 := by
  apply descent_of_endpoint
  · rw [data_16_6207.1]; exact data_16_6207.2.2
  · rw [data_16_6207.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 6247). -/
theorem data_16_6247 : oddCount 6247 16 = 10 ∧
    acceleratedOrbit 16 6247 = 5630 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_6247 : ∀ j : Fin 16,
    6247 ≤ acceleratedOrbit j.val 6247 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_6247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6247) = 59049 * m + 5630 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 6247
  rw [data_16_6247.1, data_16_6247.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_6247 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6247) < 65536 * m + 6247 := by
  apply descent_of_endpoint
  · rw [data_16_6247.1]; exact data_16_6247.2.2
  · rw [data_16_6247.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 6555). -/
theorem data_16_6555 : oddCount 6555 16 = 10 ∧
    acceleratedOrbit 16 6555 = 5908 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_6555 : ∀ j : Fin 16,
    6555 ≤ acceleratedOrbit j.val 6555 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_6555 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6555) = 59049 * m + 5908 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 6555
  rw [data_16_6555.1, data_16_6555.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_6555 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6555) < 65536 * m + 6555 := by
  apply descent_of_endpoint
  · rw [data_16_6555.1]; exact data_16_6555.2.2
  · rw [data_16_6555.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 6639). -/
theorem data_16_6639 : oddCount 6639 16 = 10 ∧
    acceleratedOrbit 16 6639 = 5983 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_6639 : ∀ j : Fin 16,
    6639 ≤ acceleratedOrbit j.val 6639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_6639 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6639) = 59049 * m + 5983 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 6639
  rw [data_16_6639.1, data_16_6639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_6639 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 6639) < 65536 * m + 6639 := by
  apply descent_of_endpoint
  · rw [data_16_6639.1]; exact data_16_6639.2.2
  · rw [data_16_6639.2.1]; decide

end Collatz.Research.FirstDescent.Batch045
