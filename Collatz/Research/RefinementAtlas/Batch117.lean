import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 117. -/
namespace Collatz.Research.RefinementAtlas.Batch117
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 186). -/
theorem data_8_186 : oddCount 186 8 = 3 ∧
    acceleratedOrbit 8 186 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_186 : gap 8 186 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_186 : threshold 8 186 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_186 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 186) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 186
  rw [data_8_186.1, data_8_186.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_186 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 186) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 186
  rw [data_8_186.1, data_8_186.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_186 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 186) < 256 * (2 * m) + 186 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 186 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_186] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 186) < 256 * (2 * m) + 186 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_186 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 186) < 256 * (2 * m + 1) + 186 := by
  apply refinement_cleared (k := 8) (r := 186) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_186]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 187). -/
theorem data_8_187 : oddCount 187 8 = 5 ∧
    acceleratedOrbit 8 187 = 179 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_187 : gap 8 187 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_187 : threshold 8 187 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_187 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 187) = 243 * (2 * m) + 179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 187
  rw [data_8_187.1, data_8_187.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_187 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 187) = 243 * (2 * m + 1) + 179 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 187
  rw [data_8_187.1, data_8_187.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_187 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 187) < 256 * (2 * m) + 187 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 187 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_187] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 187) < 256 * (2 * m) + 187 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_187 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 187) < 256 * (2 * m + 1) + 187 := by
  apply refinement_cleared (k := 8) (r := 187) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_187]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 188). -/
theorem data_8_188 : oddCount 188 8 = 5 ∧
    acceleratedOrbit 8 188 = 182 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_188 : gap 8 188 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_188 : threshold 8 188 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_188 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 188) = 243 * (2 * m) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 188
  rw [data_8_188.1, data_8_188.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_188 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 188) = 243 * (2 * m + 1) + 182 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 188
  rw [data_8_188.1, data_8_188.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_188 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 188) < 256 * (2 * m) + 188 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 188 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_188] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 188) < 256 * (2 * m) + 188 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_188 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 188) < 256 * (2 * m + 1) + 188 := by
  apply refinement_cleared (k := 8) (r := 188) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_188]; decide

end Collatz.Research.RefinementAtlas.Batch117
