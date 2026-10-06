import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 238. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch238
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 48487). -/
theorem data_20_48487 : oddCount 48487 20 = 12 ∧
    acceleratedOrbit 20 48487 = 24575 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_48487 : ∀ j : Fin 20,
    48487 ≤ acceleratedOrbit j.val 48487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_48487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 48487) = 531441 * m + 24575 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 48487
  rw [data_20_48487.1, data_20_48487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_48487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 48487) < 1048576 * m + 48487 := by
  apply descent_of_endpoint
  · rw [data_20_48487.1]; exact data_20_48487.2.2
  · rw [data_20_48487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 48539). -/
theorem data_20_48539 : oddCount 48539 20 = 12 ∧
    acceleratedOrbit 20 48539 = 24602 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_48539 : ∀ j : Fin 20,
    48539 ≤ acceleratedOrbit j.val 48539 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_48539 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 48539) = 531441 * m + 24602 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 48539
  rw [data_20_48539.1, data_20_48539.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_48539 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 48539) < 1048576 * m + 48539 := by
  apply descent_of_endpoint
  · rw [data_20_48539.1]; exact data_20_48539.2.2
  · rw [data_20_48539.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 49147). -/
theorem data_20_49147 : oddCount 49147 20 = 12 ∧
    acceleratedOrbit 20 49147 = 24910 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_49147 : ∀ j : Fin 20,
    49147 ≤ acceleratedOrbit j.val 49147 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_49147 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49147) = 531441 * m + 24910 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 49147
  rw [data_20_49147.1, data_20_49147.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_49147 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49147) < 1048576 * m + 49147 := by
  apply descent_of_endpoint
  · rw [data_20_49147.1]; exact data_20_49147.2.2
  · rw [data_20_49147.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 49179). -/
theorem data_20_49179 : oddCount 49179 20 = 12 ∧
    acceleratedOrbit 20 49179 = 24926 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_49179 : ∀ j : Fin 20,
    49179 ≤ acceleratedOrbit j.val 49179 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_49179 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49179) = 531441 * m + 24926 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 49179
  rw [data_20_49179.1, data_20_49179.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_49179 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49179) < 1048576 * m + 49179 := by
  apply descent_of_endpoint
  · rw [data_20_49179.1]; exact data_20_49179.2.2
  · rw [data_20_49179.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 49307). -/
theorem data_20_49307 : oddCount 49307 20 = 12 ∧
    acceleratedOrbit 20 49307 = 24991 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_49307 : ∀ j : Fin 20,
    49307 ≤ acceleratedOrbit j.val 49307 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_49307 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49307) = 531441 * m + 24991 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 49307
  rw [data_20_49307.1, data_20_49307.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_49307 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49307) < 1048576 * m + 49307 := by
  apply descent_of_endpoint
  · rw [data_20_49307.1]; exact data_20_49307.2.2
  · rw [data_20_49307.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 49947). -/
theorem data_20_49947 : oddCount 49947 20 = 12 ∧
    acceleratedOrbit 20 49947 = 25315 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_49947 : ∀ j : Fin 20,
    49947 ≤ acceleratedOrbit j.val 49947 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_49947 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49947) = 531441 * m + 25315 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 49947
  rw [data_20_49947.1, data_20_49947.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_49947 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 49947) < 1048576 * m + 49947 := by
  apply descent_of_endpoint
  · rw [data_20_49947.1]; exact data_20_49947.2.2
  · rw [data_20_49947.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 50639). -/
theorem data_20_50639 : oddCount 50639 20 = 12 ∧
    acceleratedOrbit 20 50639 = 25666 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_50639 : ∀ j : Fin 20,
    50639 ≤ acceleratedOrbit j.val 50639 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_50639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 50639) = 531441 * m + 25666 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 50639
  rw [data_20_50639.1, data_20_50639.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_50639 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 50639) < 1048576 * m + 50639 := by
  apply descent_of_endpoint
  · rw [data_20_50639.1]; exact data_20_50639.2.2
  · rw [data_20_50639.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 50671). -/
theorem data_20_50671 : oddCount 50671 20 = 12 ∧
    acceleratedOrbit 20 50671 = 25682 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_50671 : ∀ j : Fin 20,
    50671 ≤ acceleratedOrbit j.val 50671 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_50671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 50671) = 531441 * m + 25682 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 50671
  rw [data_20_50671.1, data_20_50671.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_50671 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 50671) < 1048576 * m + 50671 := by
  apply descent_of_endpoint
  · rw [data_20_50671.1]; exact data_20_50671.2.2
  · rw [data_20_50671.2.1]; decide

end Collatz.Research.FirstDescent.Batch238
