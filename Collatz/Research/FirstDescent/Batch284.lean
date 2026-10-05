import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 284. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch284
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 192999). -/
theorem data_20_192999 : oddCount 192999 20 = 12 ∧
    acceleratedOrbit 20 192999 = 97817 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_192999 : ∀ j : Fin 20,
    192999 ≤ acceleratedOrbit j.val 192999 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_192999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192999) = 531441 * m + 97817 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 192999
  rw [data_20_192999.1, data_20_192999.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_192999 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 192999) < 1048576 * m + 192999 := by
  apply descent_of_endpoint
  · rw [data_20_192999.1]; exact data_20_192999.2.2
  · rw [data_20_192999.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 193135). -/
theorem data_20_193135 : oddCount 193135 20 = 12 ∧
    acceleratedOrbit 20 193135 = 97886 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_193135 : ∀ j : Fin 20,
    193135 ≤ acceleratedOrbit j.val 193135 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_193135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193135) = 531441 * m + 97886 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 193135
  rw [data_20_193135.1, data_20_193135.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_193135 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193135) < 1048576 * m + 193135 := by
  apply descent_of_endpoint
  · rw [data_20_193135.1]; exact data_20_193135.2.2
  · rw [data_20_193135.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 193183). -/
theorem data_20_193183 : oddCount 193183 20 = 12 ∧
    acceleratedOrbit 20 193183 = 97910 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_193183 : ∀ j : Fin 20,
    193183 ≤ acceleratedOrbit j.val 193183 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_193183 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193183) = 531441 * m + 97910 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 193183
  rw [data_20_193183.1, data_20_193183.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_193183 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193183) < 1048576 * m + 193183 := by
  apply descent_of_endpoint
  · rw [data_20_193183.1]; exact data_20_193183.2.2
  · rw [data_20_193183.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 193471). -/
theorem data_20_193471 : oddCount 193471 20 = 12 ∧
    acceleratedOrbit 20 193471 = 98056 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_193471 : ∀ j : Fin 20,
    193471 ≤ acceleratedOrbit j.val 193471 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_193471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193471) = 531441 * m + 98056 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 193471
  rw [data_20_193471.1, data_20_193471.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_193471 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193471) < 1048576 * m + 193471 := by
  apply descent_of_endpoint
  · rw [data_20_193471.1]; exact data_20_193471.2.2
  · rw [data_20_193471.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 193727). -/
theorem data_20_193727 : oddCount 193727 20 = 12 ∧
    acceleratedOrbit 20 193727 = 98186 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_193727 : ∀ j : Fin 20,
    193727 ≤ acceleratedOrbit j.val 193727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_193727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193727) = 531441 * m + 98186 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 193727
  rw [data_20_193727.1, data_20_193727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_193727 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193727) < 1048576 * m + 193727 := by
  apply descent_of_endpoint
  · rw [data_20_193727.1]; exact data_20_193727.2.2
  · rw [data_20_193727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 193863). -/
theorem data_20_193863 : oddCount 193863 20 = 12 ∧
    acceleratedOrbit 20 193863 = 98255 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_193863 : ∀ j : Fin 20,
    193863 ≤ acceleratedOrbit j.val 193863 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_193863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193863) = 531441 * m + 98255 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 193863
  rw [data_20_193863.1, data_20_193863.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_193863 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 193863) < 1048576 * m + 193863 := by
  apply descent_of_endpoint
  · rw [data_20_193863.1]; exact data_20_193863.2.2
  · rw [data_20_193863.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 194047). -/
theorem data_20_194047 : oddCount 194047 20 = 12 ∧
    acceleratedOrbit 20 194047 = 98348 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_194047 : ∀ j : Fin 20,
    194047 ≤ acceleratedOrbit j.val 194047 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_194047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 194047) = 531441 * m + 98348 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 194047
  rw [data_20_194047.1, data_20_194047.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_194047 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 194047) < 1048576 * m + 194047 := by
  apply descent_of_endpoint
  · rw [data_20_194047.1]; exact data_20_194047.2.2
  · rw [data_20_194047.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 194331). -/
theorem data_20_194331 : oddCount 194331 20 = 12 ∧
    acceleratedOrbit 20 194331 = 98492 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_194331 : ∀ j : Fin 20,
    194331 ≤ acceleratedOrbit j.val 194331 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_194331 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 194331) = 531441 * m + 98492 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 194331
  rw [data_20_194331.1, data_20_194331.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_194331 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 194331) < 1048576 * m + 194331 := by
  apply descent_of_endpoint
  · rw [data_20_194331.1]; exact data_20_194331.2.2
  · rw [data_20_194331.2.1]; decide

end Collatz.Research.FirstDescent.Batch284
