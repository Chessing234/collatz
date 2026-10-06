import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 6. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch006
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2031). -/
theorem data_12_2031 : oddCount 2031 12 = 7 ∧
    acceleratedOrbit 12 2031 = 1085 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2031 : ∀ j : Fin 12,
    2031 ≤ acceleratedOrbit j.val 2031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2031 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2031) = 2187 * m + 1085 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2031
  rw [data_12_2031.1, data_12_2031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2031 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2031) < 4096 * m + 2031 := by
  apply descent_of_endpoint
  · rw [data_12_2031.1]; exact data_12_2031.2.2
  · rw [data_12_2031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2203). -/
theorem data_12_2203 : oddCount 2203 12 = 7 ∧
    acceleratedOrbit 12 2203 = 1177 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2203 : ∀ j : Fin 12,
    2203 ≤ acceleratedOrbit j.val 2203 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2203 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2203) = 2187 * m + 1177 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2203
  rw [data_12_2203.1, data_12_2203.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2203 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2203) < 4096 * m + 2203 := by
  apply descent_of_endpoint
  · rw [data_12_2203.1]; exact data_12_2203.2.2
  · rw [data_12_2203.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2239). -/
theorem data_12_2239 : oddCount 2239 12 = 7 ∧
    acceleratedOrbit 12 2239 = 1196 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2239 : ∀ j : Fin 12,
    2239 ≤ acceleratedOrbit j.val 2239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2239 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2239) = 2187 * m + 1196 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2239
  rw [data_12_2239.1, data_12_2239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2239 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2239) < 4096 * m + 2239 := by
  apply descent_of_endpoint
  · rw [data_12_2239.1]; exact data_12_2239.2.2
  · rw [data_12_2239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2351). -/
theorem data_12_2351 : oddCount 2351 12 = 7 ∧
    acceleratedOrbit 12 2351 = 1256 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2351 : ∀ j : Fin 12,
    2351 ≤ acceleratedOrbit j.val 2351 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2351 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2351) = 2187 * m + 1256 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2351
  rw [data_12_2351.1, data_12_2351.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2351 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2351) < 4096 * m + 2351 := by
  apply descent_of_endpoint
  · rw [data_12_2351.1]; exact data_12_2351.2.2
  · rw [data_12_2351.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2587). -/
theorem data_12_2587 : oddCount 2587 12 = 7 ∧
    acceleratedOrbit 12 2587 = 1382 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2587 : ∀ j : Fin 12,
    2587 ≤ acceleratedOrbit j.val 2587 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2587 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2587) = 2187 * m + 1382 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2587
  rw [data_12_2587.1, data_12_2587.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2587 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2587) < 4096 * m + 2587 := by
  apply descent_of_endpoint
  · rw [data_12_2587.1]; exact data_12_2587.2.2
  · rw [data_12_2587.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2591). -/
theorem data_12_2591 : oddCount 2591 12 = 7 ∧
    acceleratedOrbit 12 2591 = 1384 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2591 : ∀ j : Fin 12,
    2591 ≤ acceleratedOrbit j.val 2591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2591 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2591) = 2187 * m + 1384 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2591
  rw [data_12_2591.1, data_12_2591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2591 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2591) < 4096 * m + 2591 := by
  apply descent_of_endpoint
  · rw [data_12_2591.1]; exact data_12_2591.2.2
  · rw [data_12_2591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2907). -/
theorem data_12_2907 : oddCount 2907 12 = 7 ∧
    acceleratedOrbit 12 2907 = 1553 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2907 : ∀ j : Fin 12,
    2907 ≤ acceleratedOrbit j.val 2907 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2907 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2907) = 2187 * m + 1553 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2907
  rw [data_12_2907.1, data_12_2907.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2907 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2907) < 4096 * m + 2907 := by
  apply descent_of_endpoint
  · rw [data_12_2907.1]; exact data_12_2907.2.2
  · rw [data_12_2907.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (12, 2975). -/
theorem data_12_2975 : oddCount 2975 12 = 7 ∧
    acceleratedOrbit 12 2975 = 1589 ∧ 2187 < 4096 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_12_2975 : ∀ j : Fin 12,
    2975 ≤ acceleratedOrbit j.val 2975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_12_2975 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2975) = 2187 * m + 1589 := by
  have h := Congruence.accOrbit_pow_two_mul_add 12 m 2975
  rw [data_12_2975.1, data_12_2975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_12_2975 (m : Nat) :
    acceleratedOrbit 12 (4096 * m + 2975) < 4096 * m + 2975 := by
  apply descent_of_endpoint
  · rw [data_12_2975.1]; exact data_12_2975.2.2
  · rw [data_12_2975.2.1]; decide

end Collatz.Research.FirstDescent.Batch006
