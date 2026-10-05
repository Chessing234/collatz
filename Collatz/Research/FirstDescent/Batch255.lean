import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 255. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch255
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 99047). -/
theorem data_20_99047 : oddCount 99047 20 = 12 ∧
    acceleratedOrbit 20 99047 = 50200 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_99047 : ∀ j : Fin 20,
    99047 ≤ acceleratedOrbit j.val 99047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_99047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99047) = 531441 * m + 50200 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 99047
  rw [data_20_99047.1, data_20_99047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_99047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99047) < 1048576 * m + 99047 := by
  apply descent_of_endpoint
  · rw [data_20_99047.1]; exact data_20_99047.2.2
  · rw [data_20_99047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 99055). -/
theorem data_20_99055 : oddCount 99055 20 = 12 ∧
    acceleratedOrbit 20 99055 = 50204 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_99055 : ∀ j : Fin 20,
    99055 ≤ acceleratedOrbit j.val 99055 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_99055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99055) = 531441 * m + 50204 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 99055
  rw [data_20_99055.1, data_20_99055.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_99055 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99055) < 1048576 * m + 99055 := by
  apply descent_of_endpoint
  · rw [data_20_99055.1]; exact data_20_99055.2.2
  · rw [data_20_99055.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 99071). -/
theorem data_20_99071 : oddCount 99071 20 = 12 ∧
    acceleratedOrbit 20 99071 = 50212 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_99071 : ∀ j : Fin 20,
    99071 ≤ acceleratedOrbit j.val 99071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_99071 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99071) = 531441 * m + 50212 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 99071
  rw [data_20_99071.1, data_20_99071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_99071 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99071) < 1048576 * m + 99071 := by
  apply descent_of_endpoint
  · rw [data_20_99071.1]; exact data_20_99071.2.2
  · rw [data_20_99071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 99487). -/
theorem data_20_99487 : oddCount 99487 20 = 12 ∧
    acceleratedOrbit 20 99487 = 50423 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_99487 : ∀ j : Fin 20,
    99487 ≤ acceleratedOrbit j.val 99487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_99487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99487) = 531441 * m + 50423 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 99487
  rw [data_20_99487.1, data_20_99487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_99487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99487) < 1048576 * m + 99487 := by
  apply descent_of_endpoint
  · rw [data_20_99487.1]; exact data_20_99487.2.2
  · rw [data_20_99487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 99967). -/
theorem data_20_99967 : oddCount 99967 20 = 12 ∧
    acceleratedOrbit 20 99967 = 50666 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_99967 : ∀ j : Fin 20,
    99967 ≤ acceleratedOrbit j.val 99967 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_99967 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99967) = 531441 * m + 50666 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 99967
  rw [data_20_99967.1, data_20_99967.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_99967 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 99967) < 1048576 * m + 99967 := by
  apply descent_of_endpoint
  · rw [data_20_99967.1]; exact data_20_99967.2.2
  · rw [data_20_99967.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 101095). -/
theorem data_20_101095 : oddCount 101095 20 = 12 ∧
    acceleratedOrbit 20 101095 = 51238 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_101095 : ∀ j : Fin 20,
    101095 ≤ acceleratedOrbit j.val 101095 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_101095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 101095) = 531441 * m + 51238 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 101095
  rw [data_20_101095.1, data_20_101095.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_101095 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 101095) < 1048576 * m + 101095 := by
  apply descent_of_endpoint
  · rw [data_20_101095.1]; exact data_20_101095.2.2
  · rw [data_20_101095.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 101191). -/
theorem data_20_101191 : oddCount 101191 20 = 12 ∧
    acceleratedOrbit 20 101191 = 51287 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_101191 : ∀ j : Fin 20,
    101191 ≤ acceleratedOrbit j.val 101191 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_101191 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 101191) = 531441 * m + 51287 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 101191
  rw [data_20_101191.1, data_20_101191.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_101191 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 101191) < 1048576 * m + 101191 := by
  apply descent_of_endpoint
  · rw [data_20_101191.1]; exact data_20_101191.2.2
  · rw [data_20_101191.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 102127). -/
theorem data_20_102127 : oddCount 102127 20 = 12 ∧
    acceleratedOrbit 20 102127 = 51761 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_102127 : ∀ j : Fin 20,
    102127 ≤ acceleratedOrbit j.val 102127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_102127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 102127) = 531441 * m + 51761 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 102127
  rw [data_20_102127.1, data_20_102127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_102127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 102127) < 1048576 * m + 102127 := by
  apply descent_of_endpoint
  · rw [data_20_102127.1]; exact data_20_102127.2.2
  · rw [data_20_102127.2.1]; decide

end Collatz.Research.FirstDescent.Batch255
