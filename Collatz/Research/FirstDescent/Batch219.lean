import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 219. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch219
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 261287). -/
theorem data_18_261287 : oddCount 261287 18 = 11 ∧
    acceleratedOrbit 18 261287 = 176569 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_261287 : ∀ j : Fin 18,
    261287 ≤ acceleratedOrbit j.val 261287 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_261287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261287) = 177147 * m + 176569 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 261287
  rw [data_18_261287.1, data_18_261287.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_261287 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261287) < 262144 * m + 261287 := by
  apply descent_of_endpoint
  · rw [data_18_261287.1]; exact data_18_261287.2.2
  · rw [data_18_261287.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 261311). -/
theorem data_18_261311 : oddCount 261311 18 = 11 ∧
    acceleratedOrbit 18 261311 = 176585 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_261311 : ∀ j : Fin 18,
    261311 ≤ acceleratedOrbit j.val 261311 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_261311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261311) = 177147 * m + 176585 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 261311
  rw [data_18_261311.1, data_18_261311.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_261311 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261311) < 262144 * m + 261311 := by
  apply descent_of_endpoint
  · rw [data_18_261311.1]; exact data_18_261311.2.2
  · rw [data_18_261311.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 261371). -/
theorem data_18_261371 : oddCount 261371 18 = 11 ∧
    acceleratedOrbit 18 261371 = 176626 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_261371 : ∀ j : Fin 18,
    261371 ≤ acceleratedOrbit j.val 261371 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_261371 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261371) = 177147 * m + 176626 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 261371
  rw [data_18_261371.1, data_18_261371.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_261371 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261371) < 262144 * m + 261371 := by
  apply descent_of_endpoint
  · rw [data_18_261371.1]; exact data_18_261371.2.2
  · rw [data_18_261371.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 261599). -/
theorem data_18_261599 : oddCount 261599 18 = 11 ∧
    acceleratedOrbit 18 261599 = 176780 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_261599 : ∀ j : Fin 18,
    261599 ≤ acceleratedOrbit j.val 261599 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_261599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261599) = 177147 * m + 176780 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 261599
  rw [data_18_261599.1, data_18_261599.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_261599 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261599) < 262144 * m + 261599 := by
  apply descent_of_endpoint
  · rw [data_18_261599.1]; exact data_18_261599.2.2
  · rw [data_18_261599.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 261679). -/
theorem data_18_261679 : oddCount 261679 18 = 11 ∧
    acceleratedOrbit 18 261679 = 176834 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_261679 : ∀ j : Fin 18,
    261679 ≤ acceleratedOrbit j.val 261679 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_261679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261679) = 177147 * m + 176834 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 261679
  rw [data_18_261679.1, data_18_261679.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_261679 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 261679) < 262144 * m + 261679 := by
  apply descent_of_endpoint
  · rw [data_18_261679.1]; exact data_18_261679.2.2
  · rw [data_18_261679.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 262079). -/
theorem data_18_262079 : oddCount 262079 18 = 11 ∧
    acceleratedOrbit 18 262079 = 177104 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_262079 : ∀ j : Fin 18,
    262079 ≤ acceleratedOrbit j.val 262079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_262079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 262079) = 177147 * m + 177104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 262079
  rw [data_18_262079.1, data_18_262079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_262079 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 262079) < 262144 * m + 262079 := by
  apply descent_of_endpoint
  · rw [data_18_262079.1]; exact data_18_262079.2.2
  · rw [data_18_262079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 239). -/
theorem data_20_239 : oddCount 239 20 = 12 ∧
    acceleratedOrbit 20 239 = 122 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_239 : ∀ j : Fin 20,
    239 ≤ acceleratedOrbit j.val 239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239) = 531441 * m + 122 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 239
  rw [data_20_239.1, data_20_239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_239 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 239) < 1048576 * m + 239 := by
  apply descent_of_endpoint
  · rw [data_20_239.1]; exact data_20_239.2.2
  · rw [data_20_239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 487). -/
theorem data_20_487 : oddCount 487 20 = 12 ∧
    acceleratedOrbit 20 487 = 248 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_487 : ∀ j : Fin 20,
    487 ≤ acceleratedOrbit j.val 487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 487) = 531441 * m + 248 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 487
  rw [data_20_487.1, data_20_487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 487) < 1048576 * m + 487 := by
  apply descent_of_endpoint
  · rw [data_20_487.1]; exact data_20_487.2.2
  · rw [data_20_487.2.1]; decide

end Collatz.Research.FirstDescent.Batch219
