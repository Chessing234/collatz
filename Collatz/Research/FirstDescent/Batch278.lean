import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 278. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch278
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 178655). -/
theorem data_20_178655 : oddCount 178655 20 = 12 ∧
    acceleratedOrbit 20 178655 = 90547 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_178655 : ∀ j : Fin 20,
    178655 ≤ acceleratedOrbit j.val 178655 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_178655 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178655) = 531441 * m + 90547 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 178655
  rw [data_20_178655.1, data_20_178655.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_178655 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178655) < 1048576 * m + 178655 := by
  apply descent_of_endpoint
  · rw [data_20_178655.1]; exact data_20_178655.2.2
  · rw [data_20_178655.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 178799). -/
theorem data_20_178799 : oddCount 178799 20 = 12 ∧
    acceleratedOrbit 20 178799 = 90620 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_178799 : ∀ j : Fin 20,
    178799 ≤ acceleratedOrbit j.val 178799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_178799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178799) = 531441 * m + 90620 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 178799
  rw [data_20_178799.1, data_20_178799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_178799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178799) < 1048576 * m + 178799 := by
  apply descent_of_endpoint
  · rw [data_20_178799.1]; exact data_20_178799.2.2
  · rw [data_20_178799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 178815). -/
theorem data_20_178815 : oddCount 178815 20 = 12 ∧
    acceleratedOrbit 20 178815 = 90628 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_178815 : ∀ j : Fin 20,
    178815 ≤ acceleratedOrbit j.val 178815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_178815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178815) = 531441 * m + 90628 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 178815
  rw [data_20_178815.1, data_20_178815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_178815 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 178815) < 1048576 * m + 178815 := by
  apply descent_of_endpoint
  · rw [data_20_178815.1]; exact data_20_178815.2.2
  · rw [data_20_178815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 179231). -/
theorem data_20_179231 : oddCount 179231 20 = 12 ∧
    acceleratedOrbit 20 179231 = 90839 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_179231 : ∀ j : Fin 20,
    179231 ≤ acceleratedOrbit j.val 179231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_179231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 179231) = 531441 * m + 90839 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 179231
  rw [data_20_179231.1, data_20_179231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_179231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 179231) < 1048576 * m + 179231 := by
  apply descent_of_endpoint
  · rw [data_20_179231.1]; exact data_20_179231.2.2
  · rw [data_20_179231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 179503). -/
theorem data_20_179503 : oddCount 179503 20 = 12 ∧
    acceleratedOrbit 20 179503 = 90977 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_179503 : ∀ j : Fin 20,
    179503 ≤ acceleratedOrbit j.val 179503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_179503 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 179503) = 531441 * m + 90977 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 179503
  rw [data_20_179503.1, data_20_179503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_179503 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 179503) < 1048576 * m + 179503 := by
  apply descent_of_endpoint
  · rw [data_20_179503.1]; exact data_20_179503.2.2
  · rw [data_20_179503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 181083). -/
theorem data_20_181083 : oddCount 181083 20 = 12 ∧
    acceleratedOrbit 20 181083 = 91778 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_181083 : ∀ j : Fin 20,
    181083 ≤ acceleratedOrbit j.val 181083 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_181083 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181083) = 531441 * m + 91778 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 181083
  rw [data_20_181083.1, data_20_181083.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_181083 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181083) < 1048576 * m + 181083 := by
  apply descent_of_endpoint
  · rw [data_20_181083.1]; exact data_20_181083.2.2
  · rw [data_20_181083.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 181403). -/
theorem data_20_181403 : oddCount 181403 20 = 12 ∧
    acceleratedOrbit 20 181403 = 91940 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_181403 : ∀ j : Fin 20,
    181403 ≤ acceleratedOrbit j.val 181403 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_181403 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181403) = 531441 * m + 91940 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 181403
  rw [data_20_181403.1, data_20_181403.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_181403 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181403) < 1048576 * m + 181403 := by
  apply descent_of_endpoint
  · rw [data_20_181403.1]; exact data_20_181403.2.2
  · rw [data_20_181403.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 181727). -/
theorem data_20_181727 : oddCount 181727 20 = 12 ∧
    acceleratedOrbit 20 181727 = 92104 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_181727 : ∀ j : Fin 20,
    181727 ≤ acceleratedOrbit j.val 181727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_181727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181727) = 531441 * m + 92104 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 181727
  rw [data_20_181727.1, data_20_181727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_181727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 181727) < 1048576 * m + 181727 := by
  apply descent_of_endpoint
  · rw [data_20_181727.1]; exact data_20_181727.2.2
  · rw [data_20_181727.2.1]; decide

end Collatz.Research.FirstDescent.Batch278
