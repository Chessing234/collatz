import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 119. -/
namespace Collatz.Research.RefinementAtlas.Batch119
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 193). -/
theorem data_8_193 : oddCount 193 8 = 4 ∧
    acceleratedOrbit 8 193 = 62 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_193 : gap 8 193 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_193 : threshold 8 193 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_193 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 193) = 81 * (2 * m) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 193
  rw [data_8_193.1, data_8_193.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_193 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 193) = 81 * (2 * m + 1) + 62 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 193
  rw [data_8_193.1, data_8_193.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_193 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 193) < 256 * (2 * m) + 193 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 193 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_193] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 193) < 256 * (2 * m) + 193 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_193 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 193) < 256 * (2 * m + 1) + 193 := by
  apply refinement_cleared (k := 8) (r := 193) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_193]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 194). -/
theorem data_8_194 : oddCount 194 8 = 5 ∧
    acceleratedOrbit 8 194 = 188 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_194 : gap 8 194 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_194 : threshold 8 194 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_194 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 194) = 243 * (2 * m) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 194
  rw [data_8_194.1, data_8_194.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_194 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 194) = 243 * (2 * m + 1) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 194
  rw [data_8_194.1, data_8_194.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_194 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 194) < 256 * (2 * m) + 194 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 194 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_194] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 194) < 256 * (2 * m) + 194 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_194 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 194) < 256 * (2 * m + 1) + 194 := by
  apply refinement_cleared (k := 8) (r := 194) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_194]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 195). -/
theorem data_8_195 : oddCount 195 8 = 5 ∧
    acceleratedOrbit 8 195 = 188 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_195 : gap 8 195 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_195 : threshold 8 195 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_195 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 195) = 243 * (2 * m) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 195
  rw [data_8_195.1, data_8_195.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_195 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 195) = 243 * (2 * m + 1) + 188 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 195
  rw [data_8_195.1, data_8_195.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_195 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 195) < 256 * (2 * m) + 195 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 195 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_195] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 195) < 256 * (2 * m) + 195 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_195 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 195) < 256 * (2 * m + 1) + 195 := by
  apply refinement_cleared (k := 8) (r := 195) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_195]; decide

end Collatz.Research.RefinementAtlas.Batch119
