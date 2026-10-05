import Collatz.Research.DescentAtlas.Core

/-! Primitive first-descent cylinders, batch 136. Numerical facts are kernel checked. -/
namespace Collatz.Research.FirstDescent.Batch136
open Collatz
open Collatz.Research.DescentAtlas

/-- Exact endpoint and coefficient for the primitive cylinder (18, 74215). -/
theorem data_18_74215 : oddCount 74215 18 = 11 ∧
    acceleratedOrbit 18 74215 = 50153 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_74215 : ∀ j : Fin 18,
    74215 ≤ acceleratedOrbit j.val 74215 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_74215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74215) = 177147 * m + 50153 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 74215
  rw [data_18_74215.1, data_18_74215.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_74215 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74215) < 262144 * m + 74215 := by
  apply descent_of_endpoint
  · rw [data_18_74215.1]; exact data_18_74215.2.2
  · rw [data_18_74215.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 74223). -/
theorem data_18_74223 : oddCount 74223 18 = 11 ∧
    acceleratedOrbit 18 74223 = 50158 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_74223 : ∀ j : Fin 18,
    74223 ≤ acceleratedOrbit j.val 74223 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_74223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74223) = 177147 * m + 50158 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 74223
  rw [data_18_74223.1, data_18_74223.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_74223 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74223) < 262144 * m + 74223 := by
  apply descent_of_endpoint
  · rw [data_18_74223.1]; exact data_18_74223.2.2
  · rw [data_18_74223.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 74983). -/
theorem data_18_74983 : oddCount 74983 18 = 11 ∧
    acceleratedOrbit 18 74983 = 50672 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_74983 : ∀ j : Fin 18,
    74983 ≤ acceleratedOrbit j.val 74983 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_74983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74983) = 177147 * m + 50672 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 74983
  rw [data_18_74983.1, data_18_74983.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_74983 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 74983) < 262144 * m + 74983 := by
  apply descent_of_endpoint
  · rw [data_18_74983.1]; exact data_18_74983.2.2
  · rw [data_18_74983.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 75847). -/
theorem data_18_75847 : oddCount 75847 18 = 11 ∧
    acceleratedOrbit 18 75847 = 51256 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_75847 : ∀ j : Fin 18,
    75847 ≤ acceleratedOrbit j.val 75847 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_75847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 75847) = 177147 * m + 51256 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 75847
  rw [data_18_75847.1, data_18_75847.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_75847 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 75847) < 262144 * m + 75847 := by
  apply descent_of_endpoint
  · rw [data_18_75847.1]; exact data_18_75847.2.2
  · rw [data_18_75847.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 76007). -/
theorem data_18_76007 : oddCount 76007 18 = 11 ∧
    acceleratedOrbit 18 76007 = 51364 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_76007 : ∀ j : Fin 18,
    76007 ≤ acceleratedOrbit j.val 76007 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_76007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76007) = 177147 * m + 51364 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 76007
  rw [data_18_76007.1, data_18_76007.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_76007 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76007) < 262144 * m + 76007 := by
  apply descent_of_endpoint
  · rw [data_18_76007.1]; exact data_18_76007.2.2
  · rw [data_18_76007.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 76239). -/
theorem data_18_76239 : oddCount 76239 18 = 11 ∧
    acceleratedOrbit 18 76239 = 51521 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_76239 : ∀ j : Fin 18,
    76239 ≤ acceleratedOrbit j.val 76239 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_76239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76239) = 177147 * m + 51521 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 76239
  rw [data_18_76239.1, data_18_76239.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_76239 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76239) < 262144 * m + 76239 := by
  apply descent_of_endpoint
  · rw [data_18_76239.1]; exact data_18_76239.2.2
  · rw [data_18_76239.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 76447). -/
theorem data_18_76447 : oddCount 76447 18 = 11 ∧
    acceleratedOrbit 18 76447 = 51661 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_76447 : ∀ j : Fin 18,
    76447 ≤ acceleratedOrbit j.val 76447 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_76447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76447) = 177147 * m + 51661 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 76447
  rw [data_18_76447.1, data_18_76447.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_76447 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76447) < 262144 * m + 76447 := by
  apply descent_of_endpoint
  · rw [data_18_76447.1]; exact data_18_76447.2.2
  · rw [data_18_76447.2.1]; decide

/-- Exact endpoint and coefficient for the primitive cylinder (18, 76527). -/
theorem data_18_76527 : oddCount 76527 18 = 11 ∧
    acceleratedOrbit 18 76527 = 51715 ∧ 177147 < 262144 := by
  decide

/-- Every earlier representative iterate stays above the representative. -/
theorem prefix_18_76527 : ∀ j : Fin 18,
    76527 ≤ acceleratedOrbit j.val 76527 := by
  decide

/-- Exact endpoint for every member of this infinite cylinder. -/
theorem affine_18_76527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76527) = 177147 * m + 51715 := by
  have h := Congruence.accOrbit_pow_two_mul_add 18 m 76527
  rw [data_18_76527.1, data_18_76527.2.1] at h
  exact h

/-- Unconditional strict descent, including the zero class index. -/
theorem descent_18_76527 (m : Nat) :
    acceleratedOrbit 18 (262144 * m + 76527) < 262144 * m + 76527 := by
  apply descent_of_endpoint
  · rw [data_18_76527.1]; exact data_18_76527.2.2
  · rw [data_18_76527.2.1]; decide

end Collatz.Research.FirstDescent.Batch136
