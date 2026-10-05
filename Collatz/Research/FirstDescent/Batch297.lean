import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 297. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch297
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (20, 229935). -/
theorem data_20_229935 : oddCount 229935 20 = 12 ∧
    acceleratedOrbit 20 229935 = 116537 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_229935 : ∀ j : Fin 20,
    229935 ≤ acceleratedOrbit j.val 229935 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_229935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 229935) = 531441 * m + 116537 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 229935
  rw [data_20_229935.1, data_20_229935.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_229935 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 229935) < 1048576 * m + 229935 := by
  apply descent_of_endpoint
  · rw [data_20_229935.1]; exact data_20_229935.2.2
  · rw [data_20_229935.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 230383). -/
theorem data_20_230383 : oddCount 230383 20 = 12 ∧
    acceleratedOrbit 20 230383 = 116764 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_230383 : ∀ j : Fin 20,
    230383 ≤ acceleratedOrbit j.val 230383 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_230383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 230383) = 531441 * m + 116764 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 230383
  rw [data_20_230383.1, data_20_230383.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_230383 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 230383) < 1048576 * m + 230383 := by
  apply descent_of_endpoint
  · rw [data_20_230383.1]; exact data_20_230383.2.2
  · rw [data_20_230383.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 231167). -/
theorem data_20_231167 : oddCount 231167 20 = 12 ∧
    acceleratedOrbit 20 231167 = 117161 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_231167 : ∀ j : Fin 20,
    231167 ≤ acceleratedOrbit j.val 231167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_231167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231167) = 531441 * m + 117161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 231167
  rw [data_20_231167.1, data_20_231167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_231167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231167) < 1048576 * m + 231167 := by
  apply descent_of_endpoint
  · rw [data_20_231167.1]; exact data_20_231167.2.2
  · rw [data_20_231167.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 231295). -/
theorem data_20_231295 : oddCount 231295 20 = 12 ∧
    acceleratedOrbit 20 231295 = 117226 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_231295 : ∀ j : Fin 20,
    231295 ≤ acceleratedOrbit j.val 231295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_231295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231295) = 531441 * m + 117226 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 231295
  rw [data_20_231295.1, data_20_231295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_231295 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231295) < 1048576 * m + 231295 := by
  apply descent_of_endpoint
  · rw [data_20_231295.1]; exact data_20_231295.2.2
  · rw [data_20_231295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 231835). -/
theorem data_20_231835 : oddCount 231835 20 = 12 ∧
    acceleratedOrbit 20 231835 = 117500 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_231835 : ∀ j : Fin 20,
    231835 ≤ acceleratedOrbit j.val 231835 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_231835 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231835) = 531441 * m + 117500 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 231835
  rw [data_20_231835.1, data_20_231835.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_231835 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231835) < 1048576 * m + 231835 := by
  apply descent_of_endpoint
  · rw [data_20_231835.1]; exact data_20_231835.2.2
  · rw [data_20_231835.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 231871). -/
theorem data_20_231871 : oddCount 231871 20 = 12 ∧
    acceleratedOrbit 20 231871 = 117518 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_231871 : ∀ j : Fin 20,
    231871 ≤ acceleratedOrbit j.val 231871 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_231871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231871) = 531441 * m + 117518 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 231871
  rw [data_20_231871.1, data_20_231871.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_231871 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 231871) < 1048576 * m + 231871 := by
  apply descent_of_endpoint
  · rw [data_20_231871.1]; exact data_20_231871.2.2
  · rw [data_20_231871.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 232699). -/
theorem data_20_232699 : oddCount 232699 20 = 12 ∧
    acceleratedOrbit 20 232699 = 117938 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_232699 : ∀ j : Fin 20,
    232699 ≤ acceleratedOrbit j.val 232699 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_232699 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 232699) = 531441 * m + 117938 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 232699
  rw [data_20_232699.1, data_20_232699.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_232699 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 232699) < 1048576 * m + 232699 := by
  apply descent_of_endpoint
  · rw [data_20_232699.1]; exact data_20_232699.2.2
  · rw [data_20_232699.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (20, 233167). -/
theorem data_20_233167 : oddCount 233167 20 = 12 ∧
    acceleratedOrbit 20 233167 = 118175 ∧ 531441 < 1048576 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_20_233167 : ∀ j : Fin 20,
    233167 ≤ acceleratedOrbit j.val 233167 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_20_233167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 233167) = 531441 * m + 118175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 20 m 233167
  rw [data_20_233167.1, data_20_233167.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_20_233167 (m : Nat) :
    acceleratedOrbit 20 (1048576 * m + 233167) < 1048576 * m + 233167 := by
  apply descent_of_endpoint
  · rw [data_20_233167.1]; exact data_20_233167.2.2
  · rw [data_20_233167.2.1]; decide

end Collatz.Research.FirstDescent.Batch297
