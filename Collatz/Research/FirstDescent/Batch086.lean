import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 86. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch086
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51103). -/
theorem data_16_51103 : oddCount 51103 16 = 10 ∧
    acceleratedOrbit 16 51103 = 46046 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51103 : ∀ j : Fin 16,
    51103 ≤ acceleratedOrbit j.val 51103 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51103) = 59049 * m + 46046 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51103
  rw [data_16_51103.1, data_16_51103.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51103 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51103) < 65536 * m + 51103 := by
  apply descent_of_endpoint
  · rw [data_16_51103.1]; exact data_16_51103.2.2
  · rw [data_16_51103.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51271). -/
theorem data_16_51271 : oddCount 51271 16 = 10 ∧
    acceleratedOrbit 16 51271 = 46198 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51271 : ∀ j : Fin 16,
    51271 ≤ acceleratedOrbit j.val 51271 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51271) = 59049 * m + 46198 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51271
  rw [data_16_51271.1, data_16_51271.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51271 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51271) < 65536 * m + 51271 := by
  apply descent_of_endpoint
  · rw [data_16_51271.1]; exact data_16_51271.2.2
  · rw [data_16_51271.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51431). -/
theorem data_16_51431 : oddCount 51431 16 = 10 ∧
    acceleratedOrbit 16 51431 = 46342 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51431 : ∀ j : Fin 16,
    51431 ≤ acceleratedOrbit j.val 51431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51431) = 59049 * m + 46342 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51431
  rw [data_16_51431.1, data_16_51431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51431) < 65536 * m + 51431 := by
  apply descent_of_endpoint
  · rw [data_16_51431.1]; exact data_16_51431.2.2
  · rw [data_16_51431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51451). -/
theorem data_16_51451 : oddCount 51451 16 = 10 ∧
    acceleratedOrbit 16 51451 = 46360 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51451 : ∀ j : Fin 16,
    51451 ≤ acceleratedOrbit j.val 51451 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51451 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51451) = 59049 * m + 46360 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51451
  rw [data_16_51451.1, data_16_51451.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51451 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51451) < 65536 * m + 51451 := by
  apply descent_of_endpoint
  · rw [data_16_51451.1]; exact data_16_51451.2.2
  · rw [data_16_51451.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51455). -/
theorem data_16_51455 : oddCount 51455 16 = 10 ∧
    acceleratedOrbit 16 51455 = 46363 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51455 : ∀ j : Fin 16,
    51455 ≤ acceleratedOrbit j.val 51455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51455 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51455) = 59049 * m + 46363 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51455
  rw [data_16_51455.1, data_16_51455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51455 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51455) < 65536 * m + 51455 := by
  apply descent_of_endpoint
  · rw [data_16_51455.1]; exact data_16_51455.2.2
  · rw [data_16_51455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51611). -/
theorem data_16_51611 : oddCount 51611 16 = 10 ∧
    acceleratedOrbit 16 51611 = 46504 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51611 : ∀ j : Fin 16,
    51611 ≤ acceleratedOrbit j.val 51611 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51611 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51611) = 59049 * m + 46504 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51611
  rw [data_16_51611.1, data_16_51611.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51611 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51611) < 65536 * m + 51611 := by
  apply descent_of_endpoint
  · rw [data_16_51611.1]; exact data_16_51611.2.2
  · rw [data_16_51611.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51871). -/
theorem data_16_51871 : oddCount 51871 16 = 10 ∧
    acceleratedOrbit 16 51871 = 46738 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51871 : ∀ j : Fin 16,
    51871 ≤ acceleratedOrbit j.val 51871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51871 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51871) = 59049 * m + 46738 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51871
  rw [data_16_51871.1, data_16_51871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51871 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51871) < 65536 * m + 51871 := by
  apply descent_of_endpoint
  · rw [data_16_51871.1]; exact data_16_51871.2.2
  · rw [data_16_51871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 51951). -/
theorem data_16_51951 : oddCount 51951 16 = 10 ∧
    acceleratedOrbit 16 51951 = 46810 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_51951 : ∀ j : Fin 16,
    51951 ≤ acceleratedOrbit j.val 51951 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_51951 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51951) = 59049 * m + 46810 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 51951
  rw [data_16_51951.1, data_16_51951.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_51951 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 51951) < 65536 * m + 51951 := by
  apply descent_of_endpoint
  · rw [data_16_51951.1]; exact data_16_51951.2.2
  · rw [data_16_51951.2.1]; decide

end Collatz.Research.FirstDescent.Batch086
