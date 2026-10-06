import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 058. -/
namespace Collatz.Research.RefinementAtlas.Batch058
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 96). -/
theorem data_7_96 : oddCount 96 7 = 2 ∧
    acceleratedOrbit 7 96 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_96 : gap 7 96 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_96 : threshold 7 96 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_96 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 96) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 96
  rw [data_7_96.1, data_7_96.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_96 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 96) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 96
  rw [data_7_96.1, data_7_96.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_96 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 96) < 128 * (2 * m) + 96 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 96 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_96] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 96) < 128 * (2 * m) + 96 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_96 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 96) < 128 * (2 * m + 1) + 96 := by
  apply refinement_cleared (k := 7) (r := 96) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_96]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 98). -/
theorem data_7_98 : oddCount 98 7 = 2 ∧
    acceleratedOrbit 7 98 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_98 : gap 7 98 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_98 : threshold 7 98 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_98 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 98) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 98
  rw [data_7_98.1, data_7_98.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_98 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 98) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 98
  rw [data_7_98.1, data_7_98.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_98 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 98) < 128 * (2 * m) + 98 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 98 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_98] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 98) < 128 * (2 * m) + 98 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_98 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 98) < 128 * (2 * m + 1) + 98 := by
  apply refinement_cleared (k := 7) (r := 98) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_98]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 99). -/
theorem data_7_99 : oddCount 99 7 = 2 ∧
    acceleratedOrbit 7 99 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_99 : gap 7 99 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_99 : threshold 7 99 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_99 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 99) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 99
  rw [data_7_99.1, data_7_99.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_99 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 99) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 99
  rw [data_7_99.1, data_7_99.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_99 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 99) < 128 * (2 * m) + 99 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 99 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_99] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 99) < 128 * (2 * m) + 99 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_99 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 99) < 128 * (2 * m + 1) + 99 := by
  apply refinement_cleared (k := 7) (r := 99) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_99]; decide

end Collatz.Research.RefinementAtlas.Batch058
