import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 124. -/
namespace Collatz.Research.RefinementAtlas.Batch124
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 210). -/
theorem data_8_210 : oddCount 210 8 = 5 ∧
    acceleratedOrbit 8 210 = 202 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_210 : gap 8 210 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_210 : threshold 8 210 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_210 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 210) = 243 * (2 * m) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 210
  rw [data_8_210.1, data_8_210.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_210 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 210) = 243 * (2 * m + 1) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 210
  rw [data_8_210.1, data_8_210.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_210 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 210) < 256 * (2 * m) + 210 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 210 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_210] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 210) < 256 * (2 * m) + 210 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_210 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 210) < 256 * (2 * m + 1) + 210 := by
  apply refinement_cleared (k := 8) (r := 210) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_210]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 211). -/
theorem data_8_211 : oddCount 211 8 = 5 ∧
    acceleratedOrbit 8 211 = 202 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_211 : gap 8 211 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_211 : threshold 8 211 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_211 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 211) = 243 * (2 * m) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 211
  rw [data_8_211.1, data_8_211.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_211 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 211) = 243 * (2 * m + 1) + 202 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 211
  rw [data_8_211.1, data_8_211.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_211 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 211) < 256 * (2 * m) + 211 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 211 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_211] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 211) < 256 * (2 * m) + 211 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_211 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 211) < 256 * (2 * m + 1) + 211 := by
  apply refinement_cleared (k := 8) (r := 211) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_211]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 212). -/
theorem data_8_212 : oddCount 212 8 = 2 ∧
    acceleratedOrbit 8 212 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_212 : gap 8 212 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_212 : threshold 8 212 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_212 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 212) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 212
  rw [data_8_212.1, data_8_212.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_212 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 212) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 212
  rw [data_8_212.1, data_8_212.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_212 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 212) < 256 * (2 * m) + 212 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 212 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_212] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 212) < 256 * (2 * m) + 212 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_212 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 212) < 256 * (2 * m + 1) + 212 := by
  apply refinement_cleared (k := 8) (r := 212) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_212]; decide

end Collatz.Research.RefinementAtlas.Batch124
