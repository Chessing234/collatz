import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 125. -/
namespace Collatz.Research.RefinementAtlas.Batch125
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 213). -/
theorem data_8_213 : oddCount 213 8 = 2 ∧
    acceleratedOrbit 8 213 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_213 : gap 8 213 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_213 : threshold 8 213 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_213 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 213) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 213
  rw [data_8_213.1, data_8_213.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_213 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 213) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 213
  rw [data_8_213.1, data_8_213.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_213 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 213) < 256 * (2 * m) + 213 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 213 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_213] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 213) < 256 * (2 * m) + 213 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_213 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 213) < 256 * (2 * m + 1) + 213 := by
  apply refinement_cleared (k := 8) (r := 213) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_213]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 214). -/
theorem data_8_214 : oddCount 214 8 = 5 ∧
    acceleratedOrbit 8 214 = 206 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_214 : gap 8 214 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_214 : threshold 8 214 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_214 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 214) = 243 * (2 * m) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 214
  rw [data_8_214.1, data_8_214.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_214 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 214) = 243 * (2 * m + 1) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 214
  rw [data_8_214.1, data_8_214.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_214 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 214) < 256 * (2 * m) + 214 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 214 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_214] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 214) < 256 * (2 * m) + 214 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_214 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 214) < 256 * (2 * m + 1) + 214 := by
  apply refinement_cleared (k := 8) (r := 214) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_214]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 215). -/
theorem data_8_215 : oddCount 215 8 = 5 ∧
    acceleratedOrbit 8 215 = 206 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_215 : gap 8 215 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_215 : threshold 8 215 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_215 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 215) = 243 * (2 * m) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 215
  rw [data_8_215.1, data_8_215.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_215 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 215) = 243 * (2 * m + 1) + 206 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 215
  rw [data_8_215.1, data_8_215.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_215 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 215) < 256 * (2 * m) + 215 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 215 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_215] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 215) < 256 * (2 * m) + 215 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_215 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 215) < 256 * (2 * m + 1) + 215 := by
  apply refinement_cleared (k := 8) (r := 215) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_215]; decide

end Collatz.Research.RefinementAtlas.Batch125
