import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 130. -/
namespace Collatz.Research.RefinementAtlas.Batch130
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 232). -/
theorem data_8_232 : oddCount 232 8 = 3 ∧
    acceleratedOrbit 8 232 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_232 : gap 8 232 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_232 : threshold 8 232 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_232 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 232) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 232
  rw [data_8_232.1, data_8_232.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_232 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 232) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 232
  rw [data_8_232.1, data_8_232.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_232 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 232) < 256 * (2 * m) + 232 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 232 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_232] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 232) < 256 * (2 * m) + 232 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_232 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 232) < 256 * (2 * m + 1) + 232 := by
  apply refinement_cleared (k := 8) (r := 232) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_232]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 234). -/
theorem data_8_234 : oddCount 234 8 = 3 ∧
    acceleratedOrbit 8 234 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_234 : gap 8 234 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_234 : threshold 8 234 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_234 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 234) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 234
  rw [data_8_234.1, data_8_234.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_234 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 234) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 234
  rw [data_8_234.1, data_8_234.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_234 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 234) < 256 * (2 * m) + 234 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 234 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_234] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 234) < 256 * (2 * m) + 234 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_234 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 234) < 256 * (2 * m + 1) + 234 := by
  apply refinement_cleared (k := 8) (r := 234) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_234]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 236). -/
theorem data_8_236 : oddCount 236 8 = 4 ∧
    acceleratedOrbit 8 236 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_236 : gap 8 236 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_236 : threshold 8 236 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_236 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 236) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 236
  rw [data_8_236.1, data_8_236.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_236 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 236) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 236
  rw [data_8_236.1, data_8_236.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_236 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 236) < 256 * (2 * m) + 236 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 236 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_236] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 236) < 256 * (2 * m) + 236 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_236 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 236) < 256 * (2 * m + 1) + 236 := by
  apply refinement_cleared (k := 8) (r := 236) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_236]; decide

end Collatz.Research.RefinementAtlas.Batch130
