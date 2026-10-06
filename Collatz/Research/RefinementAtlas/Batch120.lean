import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 120. -/
namespace Collatz.Research.RefinementAtlas.Batch120
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 196). -/
theorem data_8_196 : oddCount 196 8 = 2 ∧
    acceleratedOrbit 8 196 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_196 : gap 8 196 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_196 : threshold 8 196 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_196 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 196) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 196
  rw [data_8_196.1, data_8_196.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_196 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 196) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 196
  rw [data_8_196.1, data_8_196.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_196 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 196) < 256 * (2 * m) + 196 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 196 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_196] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 196) < 256 * (2 * m) + 196 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_196 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 196) < 256 * (2 * m + 1) + 196 := by
  apply refinement_cleared (k := 8) (r := 196) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_196]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 197). -/
theorem data_8_197 : oddCount 197 8 = 2 ∧
    acceleratedOrbit 8 197 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_197 : gap 8 197 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_197 : threshold 8 197 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_197 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 197) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 197
  rw [data_8_197.1, data_8_197.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_197 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 197) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 197
  rw [data_8_197.1, data_8_197.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_197 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 197) < 256 * (2 * m) + 197 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 197 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_197] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 197) < 256 * (2 * m) + 197 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_197 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 197) < 256 * (2 * m + 1) + 197 := by
  apply refinement_cleared (k := 8) (r := 197) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_197]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 198). -/
theorem data_8_198 : oddCount 198 8 = 2 ∧
    acceleratedOrbit 8 198 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_198 : gap 8 198 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_198 : threshold 8 198 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_198 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 198) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 198
  rw [data_8_198.1, data_8_198.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_198 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 198) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 198
  rw [data_8_198.1, data_8_198.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_198 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 198) < 256 * (2 * m) + 198 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 198 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_198] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 198) < 256 * (2 * m) + 198 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_198 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 198) < 256 * (2 * m + 1) + 198 := by
  apply refinement_cleared (k := 8) (r := 198) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_198]; decide

end Collatz.Research.RefinementAtlas.Batch120
