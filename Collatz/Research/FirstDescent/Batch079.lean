import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 79. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch079
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 42911). -/
theorem data_16_42911 : oddCount 42911 16 = 10 ∧
    acceleratedOrbit 16 42911 = 38665 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_42911 : ∀ j : Fin 16,
    42911 ≤ acceleratedOrbit j.val 42911 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_42911 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42911) = 59049 * m + 38665 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 42911
  rw [data_16_42911.1, data_16_42911.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_42911 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 42911) < 65536 * m + 42911 := by
  apply descent_of_endpoint
  · rw [data_16_42911.1]; exact data_16_42911.2.2
  · rw [data_16_42911.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43071). -/
theorem data_16_43071 : oddCount 43071 16 = 10 ∧
    acceleratedOrbit 16 43071 = 38809 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43071 : ∀ j : Fin 16,
    43071 ≤ acceleratedOrbit j.val 43071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43071 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43071) = 59049 * m + 38809 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43071
  rw [data_16_43071.1, data_16_43071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43071 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43071) < 65536 * m + 43071 := by
  apply descent_of_endpoint
  · rw [data_16_43071.1]; exact data_16_43071.2.2
  · rw [data_16_43071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43111). -/
theorem data_16_43111 : oddCount 43111 16 = 10 ∧
    acceleratedOrbit 16 43111 = 38845 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43111 : ∀ j : Fin 16,
    43111 ≤ acceleratedOrbit j.val 43111 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43111 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43111) = 59049 * m + 38845 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43111
  rw [data_16_43111.1, data_16_43111.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43111 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43111) < 65536 * m + 43111 := by
  apply descent_of_endpoint
  · rw [data_16_43111.1]; exact data_16_43111.2.2
  · rw [data_16_43111.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43215). -/
theorem data_16_43215 : oddCount 43215 16 = 10 ∧
    acceleratedOrbit 16 43215 = 38939 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43215 : ∀ j : Fin 16,
    43215 ≤ acceleratedOrbit j.val 43215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43215) = 59049 * m + 38939 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43215
  rw [data_16_43215.1, data_16_43215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43215 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43215) < 65536 * m + 43215 := by
  apply descent_of_endpoint
  · rw [data_16_43215.1]; exact data_16_43215.2.2
  · rw [data_16_43215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43335). -/
theorem data_16_43335 : oddCount 43335 16 = 10 ∧
    acceleratedOrbit 16 43335 = 39047 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43335 : ∀ j : Fin 16,
    43335 ≤ acceleratedOrbit j.val 43335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43335) = 59049 * m + 39047 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43335
  rw [data_16_43335.1, data_16_43335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43335) < 65536 * m + 43335 := by
  apply descent_of_endpoint
  · rw [data_16_43335.1]; exact data_16_43335.2.2
  · rw [data_16_43335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43471). -/
theorem data_16_43471 : oddCount 43471 16 = 10 ∧
    acceleratedOrbit 16 43471 = 39170 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43471 : ∀ j : Fin 16,
    43471 ≤ acceleratedOrbit j.val 43471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43471) = 59049 * m + 39170 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43471
  rw [data_16_43471.1, data_16_43471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43471 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43471) < 65536 * m + 43471 := by
  apply descent_of_endpoint
  · rw [data_16_43471.1]; exact data_16_43471.2.2
  · rw [data_16_43471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43611). -/
theorem data_16_43611 : oddCount 43611 16 = 10 ∧
    acceleratedOrbit 16 43611 = 39296 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43611 : ∀ j : Fin 16,
    43611 ≤ acceleratedOrbit j.val 43611 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43611 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43611) = 59049 * m + 39296 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43611
  rw [data_16_43611.1, data_16_43611.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43611 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43611) < 65536 * m + 43611 := by
  apply descent_of_endpoint
  · rw [data_16_43611.1]; exact data_16_43611.2.2
  · rw [data_16_43611.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 43775). -/
theorem data_16_43775 : oddCount 43775 16 = 10 ∧
    acceleratedOrbit 16 43775 = 39443 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_43775 : ∀ j : Fin 16,
    43775 ≤ acceleratedOrbit j.val 43775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_43775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43775) = 59049 * m + 39443 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 43775
  rw [data_16_43775.1, data_16_43775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_43775 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 43775) < 65536 * m + 43775 := by
  apply descent_of_endpoint
  · rw [data_16_43775.1]; exact data_16_43775.2.2
  · rw [data_16_43775.2.1]; decide

end Collatz.Research.FirstDescent.Batch079
