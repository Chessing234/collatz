import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 081. -/
namespace Collatz.Research.RefinementAtlas.Batch081
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 64). -/
theorem data_8_64 : oddCount 64 8 = 1 ∧
    acceleratedOrbit 8 64 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_64 : gap 8 64 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_64 : threshold 8 64 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_64 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 64) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 64
  rw [data_8_64.1, data_8_64.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_64 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 64) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 64
  rw [data_8_64.1, data_8_64.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_64 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 64) < 256 * (2 * m) + 64 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 64 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_64] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 64) < 256 * (2 * m) + 64 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_64 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 64) < 256 * (2 * m + 1) + 64 := by
  apply refinement_cleared (k := 8) (r := 64) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_64]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 65). -/
theorem data_8_65 : oddCount 65 8 = 3 ∧
    acceleratedOrbit 8 65 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_65 : gap 8 65 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_65 : threshold 8 65 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_65 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 65) = 27 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 65
  rw [data_8_65.1, data_8_65.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_65 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 65) = 27 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 65
  rw [data_8_65.1, data_8_65.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_65 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 65) < 256 * (2 * m) + 65 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 65 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_65] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 65) < 256 * (2 * m) + 65 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_65 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 65) < 256 * (2 * m + 1) + 65 := by
  apply refinement_cleared (k := 8) (r := 65) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_65]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 66). -/
theorem data_8_66 : oddCount 66 8 = 4 ∧
    acceleratedOrbit 8 66 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_66 : gap 8 66 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_66 : threshold 8 66 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_66 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 66) = 81 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 66
  rw [data_8_66.1, data_8_66.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_66 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 66) = 81 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 66
  rw [data_8_66.1, data_8_66.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_66 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 66) < 256 * (2 * m) + 66 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 66 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_66] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 66) < 256 * (2 * m) + 66 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_66 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 66) < 256 * (2 * m + 1) + 66 := by
  apply refinement_cleared (k := 8) (r := 66) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_66]; decide

end Collatz.Research.RefinementAtlas.Batch081
