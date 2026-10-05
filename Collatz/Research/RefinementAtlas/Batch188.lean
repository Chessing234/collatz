import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 188. -/
namespace Collatz.Research.RefinementAtlas.Batch188
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 204). -/
theorem data_9_204 : oddCount 204 9 = 3 ∧
    acceleratedOrbit 9 204 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_204 : gap 9 204 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_204 : threshold 9 204 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_204 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 204) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 204
  rw [data_9_204.1, data_9_204.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_204 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 204) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 204
  rw [data_9_204.1, data_9_204.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_204 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 204) < 512 * (2 * m) + 204 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 204 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_204] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 204) < 512 * (2 * m) + 204 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_204 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 204) < 512 * (2 * m + 1) + 204 := by
  apply refinement_cleared (k := 9) (r := 204) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_204]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 205). -/
theorem data_9_205 : oddCount 205 9 = 3 ∧
    acceleratedOrbit 9 205 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_205 : gap 9 205 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_205 : threshold 9 205 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_205 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 205) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 205
  rw [data_9_205.1, data_9_205.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_205 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 205) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 205
  rw [data_9_205.1, data_9_205.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_205 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 205) < 512 * (2 * m) + 205 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 205 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_205] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 205) < 512 * (2 * m) + 205 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_205 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 205) < 512 * (2 * m + 1) + 205 := by
  apply refinement_cleared (k := 9) (r := 205) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_205]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 208). -/
theorem data_9_208 : oddCount 208 9 = 2 ∧
    acceleratedOrbit 9 208 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_208 : gap 9 208 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_208 : threshold 9 208 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_208 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 208) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 208
  rw [data_9_208.1, data_9_208.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_208 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 208) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 208
  rw [data_9_208.1, data_9_208.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_208 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 208) < 512 * (2 * m) + 208 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 208 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_208] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 208) < 512 * (2 * m) + 208 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_208 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 208) < 512 * (2 * m + 1) + 208 := by
  apply refinement_cleared (k := 9) (r := 208) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_208]; decide

end Collatz.Research.RefinementAtlas.Batch188
