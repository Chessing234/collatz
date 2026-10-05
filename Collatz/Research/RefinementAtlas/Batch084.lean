import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 084. -/
namespace Collatz.Research.RefinementAtlas.Batch084
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 74). -/
theorem data_8_74 : oddCount 74 8 = 4 ∧
    acceleratedOrbit 8 74 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_74 : gap 8 74 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_74 : threshold 8 74 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_74 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 74) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 74
  rw [data_8_74.1, data_8_74.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_74 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 74) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 74
  rw [data_8_74.1, data_8_74.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_74 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 74) < 256 * (2 * m) + 74 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 74 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_74] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 74) < 256 * (2 * m) + 74 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_74 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 74) < 256 * (2 * m + 1) + 74 := by
  apply refinement_cleared (k := 8) (r := 74) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_74]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 75). -/
theorem data_8_75 : oddCount 75 8 = 3 ∧
    acceleratedOrbit 8 75 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_75 : gap 8 75 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_75 : threshold 8 75 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_75 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 75) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 75
  rw [data_8_75.1, data_8_75.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_75 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 75) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 75
  rw [data_8_75.1, data_8_75.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_75 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 75) < 256 * (2 * m) + 75 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 75 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_75] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 75) < 256 * (2 * m) + 75 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_75 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 75) < 256 * (2 * m + 1) + 75 := by
  apply refinement_cleared (k := 8) (r := 75) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_75]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 76). -/
theorem data_8_76 : oddCount 76 8 = 4 ∧
    acceleratedOrbit 8 76 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_76 : gap 8 76 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_76 : threshold 8 76 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_76 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 76) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 76
  rw [data_8_76.1, data_8_76.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_76 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 76) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 76
  rw [data_8_76.1, data_8_76.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_76 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 76) < 256 * (2 * m) + 76 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 76 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_76] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 76) < 256 * (2 * m) + 76 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_76 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 76) < 256 * (2 * m + 1) + 76 := by
  apply refinement_cleared (k := 8) (r := 76) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_76]; decide

end Collatz.Research.RefinementAtlas.Batch084
