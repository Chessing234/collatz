import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 3. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch003
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (10, 423). -/
theorem data_10_423 : oddCount 423 10 = 6 ∧
    acceleratedOrbit 10 423 = 302 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_423 : ∀ j : Fin 10,
    423 ≤ acceleratedOrbit j.val 423 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_423 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 423) = 729 * m + 302 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 423
  rw [data_10_423.1, data_10_423.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_423 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 423) < 1024 * m + 423 := by
  apply descent_of_endpoint
  · rw [data_10_423.1]; exact data_10_423.2.2
  · rw [data_10_423.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 507). -/
theorem data_10_507 : oddCount 507 10 = 6 ∧
    acceleratedOrbit 10 507 = 362 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_507 : ∀ j : Fin 10,
    507 ≤ acceleratedOrbit j.val 507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_507 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 507) = 729 * m + 362 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 507
  rw [data_10_507.1, data_10_507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_507 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 507) < 1024 * m + 507 := by
  apply descent_of_endpoint
  · rw [data_10_507.1]; exact data_10_507.2.2
  · rw [data_10_507.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 575). -/
theorem data_10_575 : oddCount 575 10 = 6 ∧
    acceleratedOrbit 10 575 = 410 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_575 : ∀ j : Fin 10,
    575 ≤ acceleratedOrbit j.val 575 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_575 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 575) = 729 * m + 410 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 575
  rw [data_10_575.1, data_10_575.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_575 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 575) < 1024 * m + 575 := by
  apply descent_of_endpoint
  · rw [data_10_575.1]; exact data_10_575.2.2
  · rw [data_10_575.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 583). -/
theorem data_10_583 : oddCount 583 10 = 6 ∧
    acceleratedOrbit 10 583 = 416 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_583 : ∀ j : Fin 10,
    583 ≤ acceleratedOrbit j.val 583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_583 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 583) = 729 * m + 416 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 583
  rw [data_10_583.1, data_10_583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_583 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 583) < 1024 * m + 583 := by
  apply descent_of_endpoint
  · rw [data_10_583.1]; exact data_10_583.2.2
  · rw [data_10_583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 735). -/
theorem data_10_735 : oddCount 735 10 = 6 ∧
    acceleratedOrbit 10 735 = 524 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_735 : ∀ j : Fin 10,
    735 ≤ acceleratedOrbit j.val 735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_735 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 735) = 729 * m + 524 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 735
  rw [data_10_735.1, data_10_735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_735 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 735) < 1024 * m + 735 := by
  apply descent_of_endpoint
  · rw [data_10_735.1]; exact data_10_735.2.2
  · rw [data_10_735.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 815). -/
theorem data_10_815 : oddCount 815 10 = 6 ∧
    acceleratedOrbit 10 815 = 581 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_815 : ∀ j : Fin 10,
    815 ≤ acceleratedOrbit j.val 815 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_815 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 815) = 729 * m + 581 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 815
  rw [data_10_815.1, data_10_815.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_815 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 815) < 1024 * m + 815 := by
  apply descent_of_endpoint
  · rw [data_10_815.1]; exact data_10_815.2.2
  · rw [data_10_815.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 923). -/
theorem data_10_923 : oddCount 923 10 = 6 ∧
    acceleratedOrbit 10 923 = 658 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_923 : ∀ j : Fin 10,
    923 ≤ acceleratedOrbit j.val 923 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_923 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 923) = 729 * m + 658 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 923
  rw [data_10_923.1, data_10_923.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_923 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 923) < 1024 * m + 923 := by
  apply descent_of_endpoint
  · rw [data_10_923.1]; exact data_10_923.2.2
  · rw [data_10_923.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (10, 975). -/
theorem data_10_975 : oddCount 975 10 = 6 ∧
    acceleratedOrbit 10 975 = 695 ∧ 729 < 1024 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_10_975 : ∀ j : Fin 10,
    975 ≤ acceleratedOrbit j.val 975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_10_975 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 975) = 729 * m + 695 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 m 975
  rw [data_10_975.1, data_10_975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_10_975 (m : Nat) :
    acceleratedOrbit 10 (1024 * m + 975) < 1024 * m + 975 := by
  apply descent_of_endpoint
  · rw [data_10_975.1]; exact data_10_975.2.2
  · rw [data_10_975.2.1]; decide

end Collatz.Research.FirstDescent.Batch003
