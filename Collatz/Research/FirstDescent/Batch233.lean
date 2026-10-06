import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 233. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch233
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 35327). -/
theorem data_20_35327 : oddCount 35327 20 = 12 ∧
    acceleratedOrbit 20 35327 = 17905 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_35327 : ∀ j : Fin 20,
    35327 ≤ acceleratedOrbit j.val 35327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_35327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35327) = 531441 * m + 17905 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 35327
  rw [data_20_35327.1, data_20_35327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_35327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35327) < 1048576 * m + 35327 := by
  apply descent_of_endpoint
  · rw [data_20_35327.1]; exact data_20_35327.2.2
  · rw [data_20_35327.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 35559). -/
theorem data_20_35559 : oddCount 35559 20 = 12 ∧
    acceleratedOrbit 20 35559 = 18023 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_35559 : ∀ j : Fin 20,
    35559 ≤ acceleratedOrbit j.val 35559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_35559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35559) = 531441 * m + 18023 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 35559
  rw [data_20_35559.1, data_20_35559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_35559 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35559) < 1048576 * m + 35559 := by
  apply descent_of_endpoint
  · rw [data_20_35559.1]; exact data_20_35559.2.2
  · rw [data_20_35559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 35867). -/
theorem data_20_35867 : oddCount 35867 20 = 12 ∧
    acceleratedOrbit 20 35867 = 18179 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_35867 : ∀ j : Fin 20,
    35867 ≤ acceleratedOrbit j.val 35867 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_35867 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35867) = 531441 * m + 18179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 35867
  rw [data_20_35867.1, data_20_35867.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_35867 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35867) < 1048576 * m + 35867 := by
  apply descent_of_endpoint
  · rw [data_20_35867.1]; exact data_20_35867.2.2
  · rw [data_20_35867.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 35871). -/
theorem data_20_35871 : oddCount 35871 20 = 12 ∧
    acceleratedOrbit 20 35871 = 18181 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_35871 : ∀ j : Fin 20,
    35871 ≤ acceleratedOrbit j.val 35871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_35871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35871) = 531441 * m + 18181 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 35871
  rw [data_20_35871.1, data_20_35871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_35871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35871) < 1048576 * m + 35871 := by
  apply descent_of_endpoint
  · rw [data_20_35871.1]; exact data_20_35871.2.2
  · rw [data_20_35871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 35995). -/
theorem data_20_35995 : oddCount 35995 20 = 12 ∧
    acceleratedOrbit 20 35995 = 18244 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_35995 : ∀ j : Fin 20,
    35995 ≤ acceleratedOrbit j.val 35995 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_35995 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35995) = 531441 * m + 18244 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 35995
  rw [data_20_35995.1, data_20_35995.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_35995 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 35995) < 1048576 * m + 35995 := by
  apply descent_of_endpoint
  · rw [data_20_35995.1]; exact data_20_35995.2.2
  · rw [data_20_35995.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 36895). -/
theorem data_20_36895 : oddCount 36895 20 = 12 ∧
    acceleratedOrbit 20 36895 = 18700 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_36895 : ∀ j : Fin 20,
    36895 ≤ acceleratedOrbit j.val 36895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_36895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 36895) = 531441 * m + 18700 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 36895
  rw [data_20_36895.1, data_20_36895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_36895 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 36895) < 1048576 * m + 36895 := by
  apply descent_of_endpoint
  · rw [data_20_36895.1]; exact data_20_36895.2.2
  · rw [data_20_36895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 37359). -/
theorem data_20_37359 : oddCount 37359 20 = 12 ∧
    acceleratedOrbit 20 37359 = 18935 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_37359 : ∀ j : Fin 20,
    37359 ≤ acceleratedOrbit j.val 37359 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_37359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 37359) = 531441 * m + 18935 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 37359
  rw [data_20_37359.1, data_20_37359.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_37359 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 37359) < 1048576 * m + 37359 := by
  apply descent_of_endpoint
  · rw [data_20_37359.1]; exact data_20_37359.2.2
  · rw [data_20_37359.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 37375). -/
theorem data_20_37375 : oddCount 37375 20 = 12 ∧
    acceleratedOrbit 20 37375 = 18943 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_37375 : ∀ j : Fin 20,
    37375 ≤ acceleratedOrbit j.val 37375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_37375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 37375) = 531441 * m + 18943 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 37375
  rw [data_20_37375.1, data_20_37375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_37375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 37375) < 1048576 * m + 37375 := by
  apply descent_of_endpoint
  · rw [data_20_37375.1]; exact data_20_37375.2.2
  · rw [data_20_37375.2.1]; decide

end Collatz.Research.FirstDescent.Batch233
