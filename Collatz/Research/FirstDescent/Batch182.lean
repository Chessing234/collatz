import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 182. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch182
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 175727). -/
theorem data_18_175727 : oddCount 175727 18 = 11 ∧
    acceleratedOrbit 18 175727 = 118751 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_175727 : ∀ j : Fin 18,
    175727 ≤ acceleratedOrbit j.val 175727 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_175727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175727) = 177147 * m + 118751 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 175727
  rw [data_18_175727.1, data_18_175727.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_175727 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175727) < 262144 * m + 175727 := by
  apply descent_of_endpoint
  · rw [data_18_175727.1]; exact data_18_175727.2.2
  · rw [data_18_175727.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 175775). -/
theorem data_18_175775 : oddCount 175775 18 = 11 ∧
    acceleratedOrbit 18 175775 = 118783 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_175775 : ∀ j : Fin 18,
    175775 ≤ acceleratedOrbit j.val 175775 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_175775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175775) = 177147 * m + 118783 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 175775
  rw [data_18_175775.1, data_18_175775.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_175775 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175775) < 262144 * m + 175775 := by
  apply descent_of_endpoint
  · rw [data_18_175775.1]; exact data_18_175775.2.2
  · rw [data_18_175775.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 175847). -/
theorem data_18_175847 : oddCount 175847 18 = 11 ∧
    acceleratedOrbit 18 175847 = 118832 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_175847 : ∀ j : Fin 18,
    175847 ≤ acceleratedOrbit j.val 175847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_175847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175847) = 177147 * m + 118832 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 175847
  rw [data_18_175847.1, data_18_175847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_175847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 175847) < 262144 * m + 175847 := by
  apply descent_of_endpoint
  · rw [data_18_175847.1]; exact data_18_175847.2.2
  · rw [data_18_175847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 176335). -/
theorem data_18_176335 : oddCount 176335 18 = 11 ∧
    acceleratedOrbit 18 176335 = 119162 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_176335 : ∀ j : Fin 18,
    176335 ≤ acceleratedOrbit j.val 176335 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_176335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176335) = 177147 * m + 119162 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 176335
  rw [data_18_176335.1, data_18_176335.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_176335 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176335) < 262144 * m + 176335 := by
  apply descent_of_endpoint
  · rw [data_18_176335.1]; exact data_18_176335.2.2
  · rw [data_18_176335.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 176367). -/
theorem data_18_176367 : oddCount 176367 18 = 11 ∧
    acceleratedOrbit 18 176367 = 119183 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_176367 : ∀ j : Fin 18,
    176367 ≤ acceleratedOrbit j.val 176367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_176367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176367) = 177147 * m + 119183 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 176367
  rw [data_18_176367.1, data_18_176367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_176367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176367) < 262144 * m + 176367 := by
  apply descent_of_endpoint
  · rw [data_18_176367.1]; exact data_18_176367.2.2
  · rw [data_18_176367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 176455). -/
theorem data_18_176455 : oddCount 176455 18 = 11 ∧
    acceleratedOrbit 18 176455 = 119243 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_176455 : ∀ j : Fin 18,
    176455 ≤ acceleratedOrbit j.val 176455 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_176455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176455) = 177147 * m + 119243 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 176455
  rw [data_18_176455.1, data_18_176455.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_176455 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176455) < 262144 * m + 176455 := by
  apply descent_of_endpoint
  · rw [data_18_176455.1]; exact data_18_176455.2.2
  · rw [data_18_176455.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 176543). -/
theorem data_18_176543 : oddCount 176543 18 = 11 ∧
    acceleratedOrbit 18 176543 = 119302 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_176543 : ∀ j : Fin 18,
    176543 ≤ acceleratedOrbit j.val 176543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_176543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176543) = 177147 * m + 119302 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 176543
  rw [data_18_176543.1, data_18_176543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_176543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176543) < 262144 * m + 176543 := by
  apply descent_of_endpoint
  · rw [data_18_176543.1]; exact data_18_176543.2.2
  · rw [data_18_176543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 176615). -/
theorem data_18_176615 : oddCount 176615 18 = 11 ∧
    acceleratedOrbit 18 176615 = 119351 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_176615 : ∀ j : Fin 18,
    176615 ≤ acceleratedOrbit j.val 176615 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_176615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176615) = 177147 * m + 119351 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 176615
  rw [data_18_176615.1, data_18_176615.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_176615 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 176615) < 262144 * m + 176615 := by
  apply descent_of_endpoint
  · rw [data_18_176615.1]; exact data_18_176615.2.2
  · rw [data_18_176615.2.1]; decide

end Collatz.Research.FirstDescent.Batch182
