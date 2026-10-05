import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 184. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch184
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 180251). -/
theorem data_18_180251 : oddCount 180251 18 = 11 ∧
    acceleratedOrbit 18 180251 = 121808 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_180251 : ∀ j : Fin 18,
    180251 ≤ acceleratedOrbit j.val 180251 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_180251 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180251) = 177147 * m + 121808 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 180251
  rw [data_18_180251.1, data_18_180251.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_180251 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180251) < 262144 * m + 180251 := by
  apply descent_of_endpoint
  · rw [data_18_180251.1]; exact data_18_180251.2.2
  · rw [data_18_180251.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 180295). -/
theorem data_18_180295 : oddCount 180295 18 = 11 ∧
    acceleratedOrbit 18 180295 = 121838 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_180295 : ∀ j : Fin 18,
    180295 ≤ acceleratedOrbit j.val 180295 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_180295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180295) = 177147 * m + 121838 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 180295
  rw [data_18_180295.1, data_18_180295.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_180295 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180295) < 262144 * m + 180295 := by
  apply descent_of_endpoint
  · rw [data_18_180295.1]; exact data_18_180295.2.2
  · rw [data_18_180295.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 180463). -/
theorem data_18_180463 : oddCount 180463 18 = 11 ∧
    acceleratedOrbit 18 180463 = 121951 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_180463 : ∀ j : Fin 18,
    180463 ≤ acceleratedOrbit j.val 180463 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_180463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180463) = 177147 * m + 121951 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 180463
  rw [data_18_180463.1, data_18_180463.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_180463 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180463) < 262144 * m + 180463 := by
  apply descent_of_endpoint
  · rw [data_18_180463.1]; exact data_18_180463.2.2
  · rw [data_18_180463.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 180543). -/
theorem data_18_180543 : oddCount 180543 18 = 11 ∧
    acceleratedOrbit 18 180543 = 122005 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_180543 : ∀ j : Fin 18,
    180543 ≤ acceleratedOrbit j.val 180543 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_180543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180543) = 177147 * m + 122005 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 180543
  rw [data_18_180543.1, data_18_180543.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_180543 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180543) < 262144 * m + 180543 := by
  apply descent_of_endpoint
  · rw [data_18_180543.1]; exact data_18_180543.2.2
  · rw [data_18_180543.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 180895). -/
theorem data_18_180895 : oddCount 180895 18 = 11 ∧
    acceleratedOrbit 18 180895 = 122243 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_180895 : ∀ j : Fin 18,
    180895 ≤ acceleratedOrbit j.val 180895 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_180895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180895) = 177147 * m + 122243 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 180895
  rw [data_18_180895.1, data_18_180895.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_180895 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180895) < 262144 * m + 180895 := by
  apply descent_of_endpoint
  · rw [data_18_180895.1]; exact data_18_180895.2.2
  · rw [data_18_180895.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 180975). -/
theorem data_18_180975 : oddCount 180975 18 = 11 ∧
    acceleratedOrbit 18 180975 = 122297 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_180975 : ∀ j : Fin 18,
    180975 ≤ acceleratedOrbit j.val 180975 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_180975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180975) = 177147 * m + 122297 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 180975
  rw [data_18_180975.1, data_18_180975.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_180975 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 180975) < 262144 * m + 180975 := by
  apply descent_of_endpoint
  · rw [data_18_180975.1]; exact data_18_180975.2.2
  · rw [data_18_180975.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 181063). -/
theorem data_18_181063 : oddCount 181063 18 = 11 ∧
    acceleratedOrbit 18 181063 = 122357 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_181063 : ∀ j : Fin 18,
    181063 ≤ acceleratedOrbit j.val 181063 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_181063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 181063) = 177147 * m + 122357 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 181063
  rw [data_18_181063.1, data_18_181063.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_181063 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 181063) < 262144 * m + 181063 := by
  apply descent_of_endpoint
  · rw [data_18_181063.1]; exact data_18_181063.2.2
  · rw [data_18_181063.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 182087). -/
theorem data_18_182087 : oddCount 182087 18 = 11 ∧
    acceleratedOrbit 18 182087 = 123049 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_182087 : ∀ j : Fin 18,
    182087 ≤ acceleratedOrbit j.val 182087 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_182087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182087) = 177147 * m + 123049 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 182087
  rw [data_18_182087.1, data_18_182087.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_182087 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 182087) < 262144 * m + 182087 := by
  apply descent_of_endpoint
  · rw [data_18_182087.1]; exact data_18_182087.2.2
  · rw [data_18_182087.2.1]; decide

end Collatz.Research.FirstDescent.Batch184
