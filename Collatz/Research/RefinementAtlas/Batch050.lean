import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 050. -/
namespace Collatz.Research.RefinementAtlas.Batch050
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 64). -/
theorem data_7_64 : oddCount 64 7 = 1 ∧
    acceleratedOrbit 7 64 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_64 : gap 7 64 = 125 ∧ 3 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_64 : threshold 7 64 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_64 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 64) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 64
  rw [data_7_64.1, data_7_64.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_64 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 64) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 64
  rw [data_7_64.1, data_7_64.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_64 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 64) < 128 * (2 * m) + 64 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 64 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_64] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 64) < 128 * (2 * m) + 64 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_64 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 64) < 128 * (2 * m + 1) + 64 := by
  apply refinement_cleared (k := 7) (r := 64) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_64]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 65). -/
theorem data_7_65 : oddCount 65 7 = 3 ∧
    acceleratedOrbit 7 65 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_65 : gap 7 65 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_65 : threshold 7 65 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_65 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 65) = 27 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 65
  rw [data_7_65.1, data_7_65.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_65 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 65) = 27 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 65
  rw [data_7_65.1, data_7_65.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_65 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 65) < 128 * (2 * m) + 65 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 65 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_65] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 65) < 128 * (2 * m) + 65 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_65 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 65) < 128 * (2 * m + 1) + 65 := by
  apply refinement_cleared (k := 7) (r := 65) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_65]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 66). -/
theorem data_7_66 : oddCount 66 7 = 4 ∧
    acceleratedOrbit 7 66 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_66 : gap 7 66 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_66 : threshold 7 66 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_66 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 66) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 66
  rw [data_7_66.1, data_7_66.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_66 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 66) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 66
  rw [data_7_66.1, data_7_66.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_66 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 66) < 128 * (2 * m) + 66 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 66 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_66] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 66) < 128 * (2 * m) + 66 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_66 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 66) < 128 * (2 * m + 1) + 66 := by
  apply refinement_cleared (k := 7) (r := 66) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_66]; decide

end Collatz.Research.RefinementAtlas.Batch050
