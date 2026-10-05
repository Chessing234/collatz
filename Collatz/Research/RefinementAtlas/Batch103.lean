import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 103. -/
namespace Collatz.Research.RefinementAtlas.Batch103
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 140). -/
theorem data_8_140 : oddCount 140 8 = 2 ∧
    acceleratedOrbit 8 140 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_140 : gap 8 140 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_140 : threshold 8 140 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_140 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 140) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 140
  rw [data_8_140.1, data_8_140.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_140 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 140) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 140
  rw [data_8_140.1, data_8_140.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_140 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 140) < 256 * (2 * m) + 140 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 140 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_140] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 140) < 256 * (2 * m) + 140 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_140 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 140) < 256 * (2 * m + 1) + 140 := by
  apply refinement_cleared (k := 8) (r := 140) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_140]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 141). -/
theorem data_8_141 : oddCount 141 8 = 2 ∧
    acceleratedOrbit 8 141 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_141 : gap 8 141 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_141 : threshold 8 141 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_141 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 141) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 141
  rw [data_8_141.1, data_8_141.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_141 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 141) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 141
  rw [data_8_141.1, data_8_141.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_141 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 141) < 256 * (2 * m) + 141 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 141 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_141] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 141) < 256 * (2 * m) + 141 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_141 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 141) < 256 * (2 * m + 1) + 141 := by
  apply refinement_cleared (k := 8) (r := 141) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_141]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 142). -/
theorem data_8_142 : oddCount 142 8 = 5 ∧
    acceleratedOrbit 8 142 = 137 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_142 : gap 8 142 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_142 : threshold 8 142 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_142 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 142) = 243 * (2 * m) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 142
  rw [data_8_142.1, data_8_142.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_142 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 142) = 243 * (2 * m + 1) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 142
  rw [data_8_142.1, data_8_142.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_142 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 142) < 256 * (2 * m) + 142 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 142 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_142] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 142) < 256 * (2 * m) + 142 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_142 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 142) < 256 * (2 * m + 1) + 142 := by
  apply refinement_cleared (k := 8) (r := 142) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_142]; decide

end Collatz.Research.RefinementAtlas.Batch103
