import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 87. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch087
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52031). -/
theorem data_16_52031 : oddCount 52031 16 = 10 ∧
    acceleratedOrbit 16 52031 = 46882 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52031 : ∀ j : Fin 16,
    52031 ≤ acceleratedOrbit j.val 52031 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52031 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52031) = 59049 * m + 46882 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52031
  rw [data_16_52031.1, data_16_52031.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52031 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52031) < 65536 * m + 52031 := by
  apply descent_of_endpoint
  · rw [data_16_52031.1]; exact data_16_52031.2.2
  · rw [data_16_52031.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52071). -/
theorem data_16_52071 : oddCount 52071 16 = 10 ∧
    acceleratedOrbit 16 52071 = 46918 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52071 : ∀ j : Fin 16,
    52071 ≤ acceleratedOrbit j.val 52071 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52071 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52071) = 59049 * m + 46918 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52071
  rw [data_16_52071.1, data_16_52071.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52071 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52071) < 65536 * m + 52071 := by
  apply descent_of_endpoint
  · rw [data_16_52071.1]; exact data_16_52071.2.2
  · rw [data_16_52071.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52335). -/
theorem data_16_52335 : oddCount 52335 16 = 10 ∧
    acceleratedOrbit 16 52335 = 47156 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52335 : ∀ j : Fin 16,
    52335 ≤ acceleratedOrbit j.val 52335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52335) = 59049 * m + 47156 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52335
  rw [data_16_52335.1, data_16_52335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52335 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52335) < 65536 * m + 52335 := by
  apply descent_of_endpoint
  · rw [data_16_52335.1]; exact data_16_52335.2.2
  · rw [data_16_52335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52415). -/
theorem data_16_52415 : oddCount 52415 16 = 10 ∧
    acceleratedOrbit 16 52415 = 47228 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52415 : ∀ j : Fin 16,
    52415 ≤ acceleratedOrbit j.val 52415 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52415) = 59049 * m + 47228 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52415
  rw [data_16_52415.1, data_16_52415.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52415 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52415) < 65536 * m + 52415 := by
  apply descent_of_endpoint
  · rw [data_16_52415.1]; exact data_16_52415.2.2
  · rw [data_16_52415.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52431). -/
theorem data_16_52431 : oddCount 52431 16 = 10 ∧
    acceleratedOrbit 16 52431 = 47243 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52431 : ∀ j : Fin 16,
    52431 ≤ acceleratedOrbit j.val 52431 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52431) = 59049 * m + 47243 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52431
  rw [data_16_52431.1, data_16_52431.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52431 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52431) < 65536 * m + 52431 := by
  apply descent_of_endpoint
  · rw [data_16_52431.1]; exact data_16_52431.2.2
  · rw [data_16_52431.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52507). -/
theorem data_16_52507 : oddCount 52507 16 = 10 ∧
    acceleratedOrbit 16 52507 = 47311 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52507 : ∀ j : Fin 16,
    52507 ≤ acceleratedOrbit j.val 52507 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52507 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52507) = 59049 * m + 47311 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52507
  rw [data_16_52507.1, data_16_52507.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52507 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52507) < 65536 * m + 52507 := by
  apply descent_of_endpoint
  · rw [data_16_52507.1]; exact data_16_52507.2.2
  · rw [data_16_52507.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52551). -/
theorem data_16_52551 : oddCount 52551 16 = 10 ∧
    acceleratedOrbit 16 52551 = 47351 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52551 : ∀ j : Fin 16,
    52551 ≤ acceleratedOrbit j.val 52551 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52551) = 59049 * m + 47351 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52551
  rw [data_16_52551.1, data_16_52551.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52551 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52551) < 65536 * m + 52551 := by
  apply descent_of_endpoint
  · rw [data_16_52551.1]; exact data_16_52551.2.2
  · rw [data_16_52551.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (16, 52735). -/
theorem data_16_52735 : oddCount 52735 16 = 10 ∧
    acceleratedOrbit 16 52735 = 47516 ∧ 59049 < 65536 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_16_52735 : ∀ j : Fin 16,
    52735 ≤ acceleratedOrbit j.val 52735 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_16_52735 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52735) = 59049 * m + 47516 := by
  have h := Congruence.accOrbit_pow_two_mul_add 16 m 52735
  rw [data_16_52735.1, data_16_52735.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_16_52735 (m : Nat) :
    acceleratedOrbit 16 (65536 * m + 52735) < 65536 * m + 52735 := by
  apply descent_of_endpoint
  · rw [data_16_52735.1]; exact data_16_52735.2.2
  · rw [data_16_52735.2.1]; decide

end Collatz.Research.FirstDescent.Batch087
