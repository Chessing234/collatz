import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 133. -/
namespace Collatz.Research.RefinementAtlas.Batch133
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 244). -/
theorem data_8_244 : oddCount 244 8 = 4 ∧
    acceleratedOrbit 8 244 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_244 : gap 8 244 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_244 : threshold 8 244 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_244 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 244) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 244
  rw [data_8_244.1, data_8_244.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_244 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 244) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 244
  rw [data_8_244.1, data_8_244.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_244 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 244) < 256 * (2 * m) + 244 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 244 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_244] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 244) < 256 * (2 * m) + 244 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_244 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 244) < 256 * (2 * m + 1) + 244 := by
  apply refinement_cleared (k := 8) (r := 244) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_244]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 245). -/
theorem data_8_245 : oddCount 245 8 = 4 ∧
    acceleratedOrbit 8 245 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_245 : gap 8 245 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_245 : threshold 8 245 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_245 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 245) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 245
  rw [data_8_245.1, data_8_245.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_245 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 245) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 245
  rw [data_8_245.1, data_8_245.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_245 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 245) < 256 * (2 * m) + 245 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 245 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_245] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 245) < 256 * (2 * m) + 245 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_245 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 245) < 256 * (2 * m + 1) + 245 := by
  apply refinement_cleared (k := 8) (r := 245) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_245]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 246). -/
theorem data_8_246 : oddCount 246 8 = 5 ∧
    acceleratedOrbit 8 246 = 236 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_246 : gap 8 246 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_246 : threshold 8 246 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_246 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 246) = 243 * (2 * m) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 246
  rw [data_8_246.1, data_8_246.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_246 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 246) = 243 * (2 * m + 1) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 246
  rw [data_8_246.1, data_8_246.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_246 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 246) < 256 * (2 * m) + 246 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 246 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_246] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 246) < 256 * (2 * m) + 246 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_246 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 246) < 256 * (2 * m + 1) + 246 := by
  apply refinement_cleared (k := 8) (r := 246) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_246]; decide

end Collatz.Research.RefinementAtlas.Batch133
