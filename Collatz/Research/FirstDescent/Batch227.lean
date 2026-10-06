import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 227. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch227
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 16799). -/
theorem data_20_16799 : oddCount 16799 20 = 12 ∧
    acceleratedOrbit 20 16799 = 8515 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_16799 : ∀ j : Fin 20,
    16799 ≤ acceleratedOrbit j.val 16799 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_16799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16799) = 531441 * m + 8515 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 16799
  rw [data_20_16799.1, data_20_16799.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_16799 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16799) < 1048576 * m + 16799 := by
  apply descent_of_endpoint
  · rw [data_20_16799.1]; exact data_20_16799.2.2
  · rw [data_20_16799.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 16943). -/
theorem data_20_16943 : oddCount 16943 20 = 12 ∧
    acceleratedOrbit 20 16943 = 8588 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_16943 : ∀ j : Fin 20,
    16943 ≤ acceleratedOrbit j.val 16943 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_16943 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16943) = 531441 * m + 8588 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 16943
  rw [data_20_16943.1, data_20_16943.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_16943 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16943) < 1048576 * m + 16943 := by
  apply descent_of_endpoint
  · rw [data_20_16943.1]; exact data_20_16943.2.2
  · rw [data_20_16943.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 17215). -/
theorem data_20_17215 : oddCount 17215 20 = 12 ∧
    acceleratedOrbit 20 17215 = 8726 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_17215 : ∀ j : Fin 20,
    17215 ≤ acceleratedOrbit j.val 17215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_17215 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17215) = 531441 * m + 8726 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 17215
  rw [data_20_17215.1, data_20_17215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_17215 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17215) < 1048576 * m + 17215 := by
  apply descent_of_endpoint
  · rw [data_20_17215.1]; exact data_20_17215.2.2
  · rw [data_20_17215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 17375). -/
theorem data_20_17375 : oddCount 17375 20 = 12 ∧
    acceleratedOrbit 20 17375 = 8807 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_17375 : ∀ j : Fin 20,
    17375 ≤ acceleratedOrbit j.val 17375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_17375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17375) = 531441 * m + 8807 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 17375
  rw [data_20_17375.1, data_20_17375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_17375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17375) < 1048576 * m + 17375 := by
  apply descent_of_endpoint
  · rw [data_20_17375.1]; exact data_20_17375.2.2
  · rw [data_20_17375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 17499). -/
theorem data_20_17499 : oddCount 17499 20 = 12 ∧
    acceleratedOrbit 20 17499 = 8870 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_17499 : ∀ j : Fin 20,
    17499 ≤ acceleratedOrbit j.val 17499 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_17499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17499) = 531441 * m + 8870 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 17499
  rw [data_20_17499.1, data_20_17499.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_17499 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17499) < 1048576 * m + 17499 := by
  apply descent_of_endpoint
  · rw [data_20_17499.1]; exact data_20_17499.2.2
  · rw [data_20_17499.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 17535). -/
theorem data_20_17535 : oddCount 17535 20 = 12 ∧
    acceleratedOrbit 20 17535 = 8888 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_17535 : ∀ j : Fin 20,
    17535 ≤ acceleratedOrbit j.val 17535 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_17535 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17535) = 531441 * m + 8888 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 17535
  rw [data_20_17535.1, data_20_17535.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_17535 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 17535) < 1048576 * m + 17535 := by
  apply descent_of_endpoint
  · rw [data_20_17535.1]; exact data_20_17535.2.2
  · rw [data_20_17535.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 18127). -/
theorem data_20_18127 : oddCount 18127 20 = 12 ∧
    acceleratedOrbit 20 18127 = 9188 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_18127 : ∀ j : Fin 20,
    18127 ≤ acceleratedOrbit j.val 18127 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_18127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18127) = 531441 * m + 9188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 18127
  rw [data_20_18127.1, data_20_18127.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_18127 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18127) < 1048576 * m + 18127 := by
  apply descent_of_endpoint
  · rw [data_20_18127.1]; exact data_20_18127.2.2
  · rw [data_20_18127.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 18303). -/
theorem data_20_18303 : oddCount 18303 20 = 12 ∧
    acceleratedOrbit 20 18303 = 9277 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_18303 : ∀ j : Fin 20,
    18303 ≤ acceleratedOrbit j.val 18303 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_18303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18303) = 531441 * m + 9277 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 18303
  rw [data_20_18303.1, data_20_18303.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_18303 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 18303) < 1048576 * m + 18303 := by
  apply descent_of_endpoint
  · rw [data_20_18303.1]; exact data_20_18303.2.2
  · rw [data_20_18303.2.1]; decide

end Collatz.Research.FirstDescent.Batch227
