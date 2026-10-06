import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 226. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch226
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 13871). -/
theorem data_20_13871 : oddCount 13871 20 = 12 ∧
    acceleratedOrbit 20 13871 = 7031 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_13871 : ∀ j : Fin 20,
    13871 ≤ acceleratedOrbit j.val 13871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_13871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 13871) = 531441 * m + 7031 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 13871
  rw [data_20_13871.1, data_20_13871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_13871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 13871) < 1048576 * m + 13871 := by
  apply descent_of_endpoint
  · rw [data_20_13871.1]; exact data_20_13871.2.2
  · rw [data_20_13871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 14183). -/
theorem data_20_14183 : oddCount 14183 20 = 12 ∧
    acceleratedOrbit 20 14183 = 7189 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_14183 : ∀ j : Fin 20,
    14183 ≤ acceleratedOrbit j.val 14183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_14183 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 14183) = 531441 * m + 7189 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 14183
  rw [data_20_14183.1, data_20_14183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_14183 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 14183) < 1048576 * m + 14183 := by
  apply descent_of_endpoint
  · rw [data_20_14183.1]; exact data_20_14183.2.2
  · rw [data_20_14183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 14463). -/
theorem data_20_14463 : oddCount 14463 20 = 12 ∧
    acceleratedOrbit 20 14463 = 7331 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_14463 : ∀ j : Fin 20,
    14463 ≤ acceleratedOrbit j.val 14463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_14463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 14463) = 531441 * m + 7331 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 14463
  rw [data_20_14463.1, data_20_14463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_14463 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 14463) < 1048576 * m + 14463 := by
  apply descent_of_endpoint
  · rw [data_20_14463.1]; exact data_20_14463.2.2
  · rw [data_20_14463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 14587). -/
theorem data_20_14587 : oddCount 14587 20 = 12 ∧
    acceleratedOrbit 20 14587 = 7394 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_14587 : ∀ j : Fin 20,
    14587 ≤ acceleratedOrbit j.val 14587 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_14587 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 14587) = 531441 * m + 7394 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 14587
  rw [data_20_14587.1, data_20_14587.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_14587 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 14587) < 1048576 * m + 14587 := by
  apply descent_of_endpoint
  · rw [data_20_14587.1]; exact data_20_14587.2.2
  · rw [data_20_14587.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 15231). -/
theorem data_20_15231 : oddCount 15231 20 = 12 ∧
    acceleratedOrbit 20 15231 = 7720 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_15231 : ∀ j : Fin 20,
    15231 ≤ acceleratedOrbit j.val 15231 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_15231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 15231) = 531441 * m + 7720 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 15231
  rw [data_20_15231.1, data_20_15231.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_15231 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 15231) < 1048576 * m + 15231 := by
  apply descent_of_endpoint
  · rw [data_20_15231.1]; exact data_20_15231.2.2
  · rw [data_20_15231.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 15807). -/
theorem data_20_15807 : oddCount 15807 20 = 12 ∧
    acceleratedOrbit 20 15807 = 8012 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_15807 : ∀ j : Fin 20,
    15807 ≤ acceleratedOrbit j.val 15807 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_15807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 15807) = 531441 * m + 8012 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 15807
  rw [data_20_15807.1, data_20_15807.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_15807 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 15807) < 1048576 * m + 15807 := by
  apply descent_of_endpoint
  · rw [data_20_15807.1]; exact data_20_15807.2.2
  · rw [data_20_15807.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 16079). -/
theorem data_20_16079 : oddCount 16079 20 = 12 ∧
    acceleratedOrbit 20 16079 = 8150 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_16079 : ∀ j : Fin 20,
    16079 ≤ acceleratedOrbit j.val 16079 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_16079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16079) = 531441 * m + 8150 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 16079
  rw [data_20_16079.1, data_20_16079.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_16079 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16079) < 1048576 * m + 16079 := by
  apply descent_of_endpoint
  · rw [data_20_16079.1]; exact data_20_16079.2.2
  · rw [data_20_16079.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 16487). -/
theorem data_20_16487 : oddCount 16487 20 = 12 ∧
    acceleratedOrbit 20 16487 = 8357 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_16487 : ∀ j : Fin 20,
    16487 ≤ acceleratedOrbit j.val 16487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_16487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16487) = 531441 * m + 8357 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 16487
  rw [data_20_16487.1, data_20_16487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_16487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 16487) < 1048576 * m + 16487 := by
  apply descent_of_endpoint
  · rw [data_20_16487.1]; exact data_20_16487.2.2
  · rw [data_20_16487.2.1]; decide

end Collatz.Research.FirstDescent.Batch226
