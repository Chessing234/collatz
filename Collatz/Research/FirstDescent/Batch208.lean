import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 208. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch208
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 233711). -/
theorem data_18_233711 : oddCount 233711 18 = 11 ∧
    acceleratedOrbit 18 233711 = 157934 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_233711 : ∀ j : Fin 18,
    233711 ≤ acceleratedOrbit j.val 233711 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_233711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233711) = 177147 * m + 157934 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 233711
  rw [data_18_233711.1, data_18_233711.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_233711 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233711) < 262144 * m + 233711 := by
  apply descent_of_endpoint
  · rw [data_18_233711.1]; exact data_18_233711.2.2
  · rw [data_18_233711.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 233755). -/
theorem data_18_233755 : oddCount 233755 18 = 11 ∧
    acceleratedOrbit 18 233755 = 157964 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_233755 : ∀ j : Fin 18,
    233755 ≤ acceleratedOrbit j.val 233755 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_233755 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233755) = 177147 * m + 157964 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 233755
  rw [data_18_233755.1, data_18_233755.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_233755 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 233755) < 262144 * m + 233755 := by
  apply descent_of_endpoint
  · rw [data_18_233755.1]; exact data_18_233755.2.2
  · rw [data_18_233755.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 235367). -/
theorem data_18_235367 : oddCount 235367 18 = 11 ∧
    acceleratedOrbit 18 235367 = 159053 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_235367 : ∀ j : Fin 18,
    235367 ≤ acceleratedOrbit j.val 235367 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_235367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 235367) = 177147 * m + 159053 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 235367
  rw [data_18_235367.1, data_18_235367.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_235367 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 235367) < 262144 * m + 235367 := by
  apply descent_of_endpoint
  · rw [data_18_235367.1]; exact data_18_235367.2.2
  · rw [data_18_235367.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 235547). -/
theorem data_18_235547 : oddCount 235547 18 = 11 ∧
    acceleratedOrbit 18 235547 = 159175 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_235547 : ∀ j : Fin 18,
    235547 ≤ acceleratedOrbit j.val 235547 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_235547 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 235547) = 177147 * m + 159175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 235547
  rw [data_18_235547.1, data_18_235547.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_235547 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 235547) < 262144 * m + 235547 := by
  apply descent_of_endpoint
  · rw [data_18_235547.1]; exact data_18_235547.2.2
  · rw [data_18_235547.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 236015). -/
theorem data_18_236015 : oddCount 236015 18 = 11 ∧
    acceleratedOrbit 18 236015 = 159491 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_236015 : ∀ j : Fin 18,
    236015 ≤ acceleratedOrbit j.val 236015 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_236015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 236015) = 177147 * m + 159491 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 236015
  rw [data_18_236015.1, data_18_236015.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_236015 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 236015) < 262144 * m + 236015 := by
  apply descent_of_endpoint
  · rw [data_18_236015.1]; exact data_18_236015.2.2
  · rw [data_18_236015.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 236827). -/
theorem data_18_236827 : oddCount 236827 18 = 11 ∧
    acceleratedOrbit 18 236827 = 160040 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_236827 : ∀ j : Fin 18,
    236827 ≤ acceleratedOrbit j.val 236827 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_236827 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 236827) = 177147 * m + 160040 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 236827
  rw [data_18_236827.1, data_18_236827.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_236827 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 236827) < 262144 * m + 236827 := by
  apply descent_of_endpoint
  · rw [data_18_236827.1]; exact data_18_236827.2.2
  · rw [data_18_236827.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 236903). -/
theorem data_18_236903 : oddCount 236903 18 = 11 ∧
    acceleratedOrbit 18 236903 = 160091 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_236903 : ∀ j : Fin 18,
    236903 ≤ acceleratedOrbit j.val 236903 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_236903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 236903) = 177147 * m + 160091 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 236903
  rw [data_18_236903.1, data_18_236903.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_236903 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 236903) < 262144 * m + 236903 := by
  apply descent_of_endpoint
  · rw [data_18_236903.1]; exact data_18_236903.2.2
  · rw [data_18_236903.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 237039). -/
theorem data_18_237039 : oddCount 237039 18 = 11 ∧
    acceleratedOrbit 18 237039 = 160183 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_237039 : ∀ j : Fin 18,
    237039 ≤ acceleratedOrbit j.val 237039 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_237039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237039) = 177147 * m + 160183 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 237039
  rw [data_18_237039.1, data_18_237039.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_237039 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 237039) < 262144 * m + 237039 := by
  apply descent_of_endpoint
  · rw [data_18_237039.1]; exact data_18_237039.2.2
  · rw [data_18_237039.2.1]; decide

end Collatz.Research.FirstDescent.Batch208
