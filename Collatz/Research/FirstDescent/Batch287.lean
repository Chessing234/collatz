import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 287. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch287
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 199419). -/
theorem data_20_199419 : oddCount 199419 20 = 12 ∧
    acceleratedOrbit 20 199419 = 101071 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_199419 : ∀ j : Fin 20,
    199419 ≤ acceleratedOrbit j.val 199419 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_199419 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199419) = 531441 * m + 101071 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 199419
  rw [data_20_199419.1, data_20_199419.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_199419 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199419) < 1048576 * m + 199419 := by
  apply descent_of_endpoint
  · rw [data_20_199419.1]; exact data_20_199419.2.2
  · rw [data_20_199419.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 199919). -/
theorem data_20_199919 : oddCount 199919 20 = 12 ∧
    acceleratedOrbit 20 199919 = 101324 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_199919 : ∀ j : Fin 20,
    199919 ≤ acceleratedOrbit j.val 199919 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_199919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199919) = 531441 * m + 101324 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 199919
  rw [data_20_199919.1, data_20_199919.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_199919 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199919) < 1048576 * m + 199919 := by
  apply descent_of_endpoint
  · rw [data_20_199919.1]; exact data_20_199919.2.2
  · rw [data_20_199919.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 199935). -/
theorem data_20_199935 : oddCount 199935 20 = 12 ∧
    acceleratedOrbit 20 199935 = 101332 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_199935 : ∀ j : Fin 20,
    199935 ≤ acceleratedOrbit j.val 199935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_199935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199935) = 531441 * m + 101332 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 199935
  rw [data_20_199935.1, data_20_199935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_199935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 199935) < 1048576 * m + 199935 := by
  apply descent_of_endpoint
  · rw [data_20_199935.1]; exact data_20_199935.2.2
  · rw [data_20_199935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 200007). -/
theorem data_20_200007 : oddCount 200007 20 = 12 ∧
    acceleratedOrbit 20 200007 = 101369 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_200007 : ∀ j : Fin 20,
    200007 ≤ acceleratedOrbit j.val 200007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_200007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 200007) = 531441 * m + 101369 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 200007
  rw [data_20_200007.1, data_20_200007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_200007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 200007) < 1048576 * m + 200007 := by
  apply descent_of_endpoint
  · rw [data_20_200007.1]; exact data_20_200007.2.2
  · rw [data_20_200007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 200475). -/
theorem data_20_200475 : oddCount 200475 20 = 12 ∧
    acceleratedOrbit 20 200475 = 101606 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_200475 : ∀ j : Fin 20,
    200475 ≤ acceleratedOrbit j.val 200475 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_200475 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 200475) = 531441 * m + 101606 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 200475
  rw [data_20_200475.1, data_20_200475.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_200475 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 200475) < 1048576 * m + 200475 := by
  apply descent_of_endpoint
  · rw [data_20_200475.1]; exact data_20_200475.2.2
  · rw [data_20_200475.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 200751). -/
theorem data_20_200751 : oddCount 200751 20 = 12 ∧
    acceleratedOrbit 20 200751 = 101746 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_200751 : ∀ j : Fin 20,
    200751 ≤ acceleratedOrbit j.val 200751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_200751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 200751) = 531441 * m + 101746 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 200751
  rw [data_20_200751.1, data_20_200751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_200751 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 200751) < 1048576 * m + 200751 := by
  apply descent_of_endpoint
  · rw [data_20_200751.1]; exact data_20_200751.2.2
  · rw [data_20_200751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 201007). -/
theorem data_20_201007 : oddCount 201007 20 = 12 ∧
    acceleratedOrbit 20 201007 = 101876 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_201007 : ∀ j : Fin 20,
    201007 ≤ acceleratedOrbit j.val 201007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_201007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201007) = 531441 * m + 101876 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 201007
  rw [data_20_201007.1, data_20_201007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_201007 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201007) < 1048576 * m + 201007 := by
  apply descent_of_endpoint
  · rw [data_20_201007.1]; exact data_20_201007.2.2
  · rw [data_20_201007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 201327). -/
theorem data_20_201327 : oddCount 201327 20 = 12 ∧
    acceleratedOrbit 20 201327 = 102038 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_201327 : ∀ j : Fin 20,
    201327 ≤ acceleratedOrbit j.val 201327 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_201327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201327) = 531441 * m + 102038 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 201327
  rw [data_20_201327.1, data_20_201327.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_201327 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 201327) < 1048576 * m + 201327 := by
  apply descent_of_endpoint
  · rw [data_20_201327.1]; exact data_20_201327.2.2
  · rw [data_20_201327.2.1]; decide

end Collatz.Research.FirstDescent.Batch287
