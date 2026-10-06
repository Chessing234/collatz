import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 266. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch266
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 139375). -/
theorem data_20_139375 : oddCount 139375 20 = 12 ∧
    acceleratedOrbit 20 139375 = 70639 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_139375 : ∀ j : Fin 20,
    139375 ≤ acceleratedOrbit j.val 139375 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_139375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139375) = 531441 * m + 70639 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 139375
  rw [data_20_139375.1, data_20_139375.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_139375 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139375) < 1048576 * m + 139375 := by
  apply descent_of_endpoint
  · rw [data_20_139375.1]; exact data_20_139375.2.2
  · rw [data_20_139375.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 139487). -/
theorem data_20_139487 : oddCount 139487 20 = 12 ∧
    acceleratedOrbit 20 139487 = 70696 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_139487 : ∀ j : Fin 20,
    139487 ≤ acceleratedOrbit j.val 139487 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_139487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139487) = 531441 * m + 70696 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 139487
  rw [data_20_139487.1, data_20_139487.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_139487 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139487) < 1048576 * m + 139487 := by
  apply descent_of_endpoint
  · rw [data_20_139487.1]; exact data_20_139487.2.2
  · rw [data_20_139487.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 139931). -/
theorem data_20_139931 : oddCount 139931 20 = 12 ∧
    acceleratedOrbit 20 139931 = 70921 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_139931 : ∀ j : Fin 20,
    139931 ≤ acceleratedOrbit j.val 139931 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_139931 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139931) = 531441 * m + 70921 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 139931
  rw [data_20_139931.1, data_20_139931.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_139931 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 139931) < 1048576 * m + 139931 := by
  apply descent_of_endpoint
  · rw [data_20_139931.1]; exact data_20_139931.2.2
  · rw [data_20_139931.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 140027). -/
theorem data_20_140027 : oddCount 140027 20 = 12 ∧
    acceleratedOrbit 20 140027 = 70970 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_140027 : ∀ j : Fin 20,
    140027 ≤ acceleratedOrbit j.val 140027 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_140027 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 140027) = 531441 * m + 70970 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 140027
  rw [data_20_140027.1, data_20_140027.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_140027 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 140027) < 1048576 * m + 140027 := by
  apply descent_of_endpoint
  · rw [data_20_140027.1]; exact data_20_140027.2.2
  · rw [data_20_140027.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 140543). -/
theorem data_20_140543 : oddCount 140543 20 = 12 ∧
    acceleratedOrbit 20 140543 = 71231 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_140543 : ∀ j : Fin 20,
    140543 ≤ acceleratedOrbit j.val 140543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_140543 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 140543) = 531441 * m + 71231 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 140543
  rw [data_20_140543.1, data_20_140543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_140543 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 140543) < 1048576 * m + 140543 := by
  apply descent_of_endpoint
  · rw [data_20_140543.1]; exact data_20_140543.2.2
  · rw [data_20_140543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 140703). -/
theorem data_20_140703 : oddCount 140703 20 = 12 ∧
    acceleratedOrbit 20 140703 = 71312 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_140703 : ∀ j : Fin 20,
    140703 ≤ acceleratedOrbit j.val 140703 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_140703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 140703) = 531441 * m + 71312 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 140703
  rw [data_20_140703.1, data_20_140703.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_140703 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 140703) < 1048576 * m + 140703 := by
  apply descent_of_endpoint
  · rw [data_20_140703.1]; exact data_20_140703.2.2
  · rw [data_20_140703.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 141423). -/
theorem data_20_141423 : oddCount 141423 20 = 12 ∧
    acceleratedOrbit 20 141423 = 71677 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_141423 : ∀ j : Fin 20,
    141423 ≤ acceleratedOrbit j.val 141423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_141423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 141423) = 531441 * m + 71677 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 141423
  rw [data_20_141423.1, data_20_141423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_141423 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 141423) < 1048576 * m + 141423 := by
  apply descent_of_endpoint
  · rw [data_20_141423.1]; exact data_20_141423.2.2
  · rw [data_20_141423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 141519). -/
theorem data_20_141519 : oddCount 141519 20 = 12 ∧
    acceleratedOrbit 20 141519 = 71726 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_141519 : ∀ j : Fin 20,
    141519 ≤ acceleratedOrbit j.val 141519 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_141519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 141519) = 531441 * m + 71726 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 141519
  rw [data_20_141519.1, data_20_141519.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_141519 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 141519) < 1048576 * m + 141519 := by
  apply descent_of_endpoint
  · rw [data_20_141519.1]; exact data_20_141519.2.2
  · rw [data_20_141519.2.1]; decide

end Collatz.Research.FirstDescent.Batch266
