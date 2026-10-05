import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 176. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch176
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162559). -/
theorem data_18_162559 : oddCount 162559 18 = 11 ∧
    acceleratedOrbit 18 162559 = 109852 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162559 : ∀ j : Fin 18,
    162559 ≤ acceleratedOrbit j.val 162559 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162559) = 177147 * m + 109852 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162559
  rw [data_18_162559.1, data_18_162559.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162559 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162559) < 262144 * m + 162559 := by
  apply descent_of_endpoint
  · rw [data_18_162559.1]; exact data_18_162559.2.2
  · rw [data_18_162559.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162591). -/
theorem data_18_162591 : oddCount 162591 18 = 11 ∧
    acceleratedOrbit 18 162591 = 109874 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162591 : ∀ j : Fin 18,
    162591 ≤ acceleratedOrbit j.val 162591 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162591) = 177147 * m + 109874 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162591
  rw [data_18_162591.1, data_18_162591.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162591 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162591) < 262144 * m + 162591 := by
  apply descent_of_endpoint
  · rw [data_18_162591.1]; exact data_18_162591.2.2
  · rw [data_18_162591.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 162751). -/
theorem data_18_162751 : oddCount 162751 18 = 11 ∧
    acceleratedOrbit 18 162751 = 109982 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_162751 : ∀ j : Fin 18,
    162751 ≤ acceleratedOrbit j.val 162751 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_162751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162751) = 177147 * m + 109982 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 162751
  rw [data_18_162751.1, data_18_162751.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_162751 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 162751) < 262144 * m + 162751 := by
  apply descent_of_endpoint
  · rw [data_18_162751.1]; exact data_18_162751.2.2
  · rw [data_18_162751.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 163483). -/
theorem data_18_163483 : oddCount 163483 18 = 11 ∧
    acceleratedOrbit 18 163483 = 110477 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_163483 : ∀ j : Fin 18,
    163483 ≤ acceleratedOrbit j.val 163483 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_163483 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 163483) = 177147 * m + 110477 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 163483
  rw [data_18_163483.1, data_18_163483.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_163483 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 163483) < 262144 * m + 163483 := by
  apply descent_of_endpoint
  · rw [data_18_163483.1]; exact data_18_163483.2.2
  · rw [data_18_163483.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 164167). -/
theorem data_18_164167 : oddCount 164167 18 = 11 ∧
    acceleratedOrbit 18 164167 = 110939 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_164167 : ∀ j : Fin 18,
    164167 ≤ acceleratedOrbit j.val 164167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_164167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164167) = 177147 * m + 110939 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 164167
  rw [data_18_164167.1, data_18_164167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_164167 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164167) < 262144 * m + 164167 := by
  apply descent_of_endpoint
  · rw [data_18_164167.1]; exact data_18_164167.2.2
  · rw [data_18_164167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 164583). -/
theorem data_18_164583 : oddCount 164583 18 = 11 ∧
    acceleratedOrbit 18 164583 = 111220 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_164583 : ∀ j : Fin 18,
    164583 ≤ acceleratedOrbit j.val 164583 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_164583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164583) = 177147 * m + 111220 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 164583
  rw [data_18_164583.1, data_18_164583.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_164583 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164583) < 262144 * m + 164583 := by
  apply descent_of_endpoint
  · rw [data_18_164583.1]; exact data_18_164583.2.2
  · rw [data_18_164583.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 164607). -/
theorem data_18_164607 : oddCount 164607 18 = 11 ∧
    acceleratedOrbit 18 164607 = 111236 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_164607 : ∀ j : Fin 18,
    164607 ≤ acceleratedOrbit j.val 164607 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_164607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164607) = 177147 * m + 111236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 164607
  rw [data_18_164607.1, data_18_164607.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_164607 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164607) < 262144 * m + 164607 := by
  apply descent_of_endpoint
  · rw [data_18_164607.1]; exact data_18_164607.2.2
  · rw [data_18_164607.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 164699). -/
theorem data_18_164699 : oddCount 164699 18 = 11 ∧
    acceleratedOrbit 18 164699 = 111299 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_164699 : ∀ j : Fin 18,
    164699 ≤ acceleratedOrbit j.val 164699 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_164699 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164699) = 177147 * m + 111299 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 164699
  rw [data_18_164699.1, data_18_164699.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_164699 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 164699) < 262144 * m + 164699 := by
  apply descent_of_endpoint
  · rw [data_18_164699.1]; exact data_18_164699.2.2
  · rw [data_18_164699.2.1]; decide

end Collatz.Research.FirstDescent.Batch176
