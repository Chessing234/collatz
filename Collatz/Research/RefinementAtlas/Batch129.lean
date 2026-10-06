import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 129. -/
namespace Collatz.Research.RefinementAtlas.Batch129
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 228). -/
theorem data_8_228 : oddCount 228 8 = 4 ∧
    acceleratedOrbit 8 228 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_228 : gap 8 228 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_228 : threshold 8 228 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_228 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 228) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 228
  rw [data_8_228.1, data_8_228.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_228 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 228) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 228
  rw [data_8_228.1, data_8_228.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_228 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 228) < 256 * (2 * m) + 228 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 228 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_228] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 228) < 256 * (2 * m) + 228 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_228 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 228) < 256 * (2 * m + 1) + 228 := by
  apply refinement_cleared (k := 8) (r := 228) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_228]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 229). -/
theorem data_8_229 : oddCount 229 8 = 4 ∧
    acceleratedOrbit 8 229 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_229 : gap 8 229 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_229 : threshold 8 229 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_229 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 229) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 229
  rw [data_8_229.1, data_8_229.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_229 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 229) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 229
  rw [data_8_229.1, data_8_229.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_229 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 229) < 256 * (2 * m) + 229 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 229 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_229] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 229) < 256 * (2 * m) + 229 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_229 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 229) < 256 * (2 * m + 1) + 229 := by
  apply refinement_cleared (k := 8) (r := 229) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_229]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 230). -/
theorem data_8_230 : oddCount 230 8 = 4 ∧
    acceleratedOrbit 8 230 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_230 : gap 8 230 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_230 : threshold 8 230 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_230 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 230) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 230
  rw [data_8_230.1, data_8_230.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_230 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 230) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 230
  rw [data_8_230.1, data_8_230.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_230 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 230) < 256 * (2 * m) + 230 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 230 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_230] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 230) < 256 * (2 * m) + 230 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_230 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 230) < 256 * (2 * m + 1) + 230 := by
  apply refinement_cleared (k := 8) (r := 230) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_230]; decide

end Collatz.Research.RefinementAtlas.Batch129
