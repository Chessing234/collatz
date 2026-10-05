import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 228. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch228
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 18503). -/
theorem data_20_18503 : oddCount 18503 20 = 12 ∧
    acceleratedOrbit 20 18503 = 9379 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_18503 : ∀ j : Fin 20,
    18503 ≤ acceleratedOrbit j.val 18503 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_18503 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18503) = 531441 * m + 9379 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 18503
  rw [data_20_18503.1, data_20_18503.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_18503 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18503) < 1048576 * m + 18503 := by
  apply descent_of_endpoint
  · rw [data_20_18503.1]; exact data_20_18503.2.2
  · rw [data_20_18503.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 18663). -/
theorem data_20_18663 : oddCount 18663 20 = 12 ∧
    acceleratedOrbit 20 18663 = 9460 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_18663 : ∀ j : Fin 20,
    18663 ≤ acceleratedOrbit j.val 18663 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_18663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18663) = 531441 * m + 9460 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 18663
  rw [data_20_18663.1, data_20_18663.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_18663 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18663) < 1048576 * m + 18663 := by
  apply descent_of_endpoint
  · rw [data_20_18663.1]; exact data_20_18663.2.2
  · rw [data_20_18663.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 18879). -/
theorem data_20_18879 : oddCount 18879 20 = 12 ∧
    acceleratedOrbit 20 18879 = 9569 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_18879 : ∀ j : Fin 20,
    18879 ≤ acceleratedOrbit j.val 18879 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_18879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18879) = 531441 * m + 9569 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 18879
  rw [data_20_18879.1, data_20_18879.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_18879 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18879) < 1048576 * m + 18879 := by
  apply descent_of_endpoint
  · rw [data_20_18879.1]; exact data_20_18879.2.2
  · rw [data_20_18879.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 19303). -/
theorem data_20_19303 : oddCount 19303 20 = 12 ∧
    acceleratedOrbit 20 19303 = 9784 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_19303 : ∀ j : Fin 20,
    19303 ≤ acceleratedOrbit j.val 19303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_19303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 19303) = 531441 * m + 9784 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 19303
  rw [data_20_19303.1, data_20_19303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_19303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 19303) < 1048576 * m + 19303 := by
  apply descent_of_endpoint
  · rw [data_20_19303.1]; exact data_20_19303.2.2
  · rw [data_20_19303.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 19995). -/
theorem data_20_19995 : oddCount 19995 20 = 12 ∧
    acceleratedOrbit 20 19995 = 10135 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_19995 : ∀ j : Fin 20,
    19995 ≤ acceleratedOrbit j.val 19995 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_19995 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 19995) = 531441 * m + 10135 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 19995
  rw [data_20_19995.1, data_20_19995.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_19995 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 19995) < 1048576 * m + 19995 := by
  apply descent_of_endpoint
  · rw [data_20_19995.1]; exact data_20_19995.2.2
  · rw [data_20_19995.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 20223). -/
theorem data_20_20223 : oddCount 20223 20 = 12 ∧
    acceleratedOrbit 20 20223 = 10250 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_20223 : ∀ j : Fin 20,
    20223 ≤ acceleratedOrbit j.val 20223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_20223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 20223) = 531441 * m + 10250 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 20223
  rw [data_20_20223.1, data_20_20223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_20223 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 20223) < 1048576 * m + 20223 := by
  apply descent_of_endpoint
  · rw [data_20_20223.1]; exact data_20_20223.2.2
  · rw [data_20_20223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 20571). -/
theorem data_20_20571 : oddCount 20571 20 = 12 ∧
    acceleratedOrbit 20 20571 = 10427 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_20571 : ∀ j : Fin 20,
    20571 ≤ acceleratedOrbit j.val 20571 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_20571 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 20571) = 531441 * m + 10427 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 20571
  rw [data_20_20571.1, data_20_20571.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_20571 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 20571) < 1048576 * m + 20571 := by
  apply descent_of_endpoint
  · rw [data_20_20571.1]; exact data_20_20571.2.2
  · rw [data_20_20571.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 21019). -/
theorem data_20_21019 : oddCount 21019 20 = 12 ∧
    acceleratedOrbit 20 21019 = 10654 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_21019 : ∀ j : Fin 20,
    21019 ≤ acceleratedOrbit j.val 21019 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_21019 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 21019) = 531441 * m + 10654 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 21019
  rw [data_20_21019.1, data_20_21019.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_21019 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 21019) < 1048576 * m + 21019 := by
  apply descent_of_endpoint
  · rw [data_20_21019.1]; exact data_20_21019.2.2
  · rw [data_20_21019.2.1]; decide

end Collatz.Research.FirstDescent.Batch228
