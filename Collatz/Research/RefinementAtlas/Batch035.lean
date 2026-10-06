import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 035. -/
namespace Collatz.Research.RefinementAtlas.Batch035
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 10). -/
theorem data_7_10 : oddCount 10 7 = 2 ∧
    acceleratedOrbit 7 10 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_10 : gap 7 10 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_10 : threshold 7 10 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_10 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 10) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 10
  rw [data_7_10.1, data_7_10.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_10 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 10) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 10
  rw [data_7_10.1, data_7_10.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_10 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 10) < 128 * (2 * m) + 10 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 10 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_10] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 10) < 128 * (2 * m) + 10 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_10 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 10) < 128 * (2 * m + 1) + 10 := by
  apply refinement_cleared (k := 7) (r := 10) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_10]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 11). -/
theorem data_7_11 : oddCount 11 7 = 4 ∧
    acceleratedOrbit 7 11 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_11 : gap 7 11 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_11 : threshold 7 11 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_11 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 11) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 11
  rw [data_7_11.1, data_7_11.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_11 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 11) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 11
  rw [data_7_11.1, data_7_11.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_11 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 11) < 128 * (2 * m) + 11 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 11 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_11] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 11) < 128 * (2 * m) + 11 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_11 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 11) < 128 * (2 * m + 1) + 11 := by
  apply refinement_cleared (k := 7) (r := 11) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_11]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 12). -/
theorem data_7_12 : oddCount 12 7 = 2 ∧
    acceleratedOrbit 7 12 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_12 : gap 7 12 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_12 : threshold 7 12 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_12 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 12) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 12
  rw [data_7_12.1, data_7_12.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_12 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 12) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 12
  rw [data_7_12.1, data_7_12.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_12 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 12) < 128 * (2 * m) + 12 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 12 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_12] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 12) < 128 * (2 * m) + 12 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_12 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 12) < 128 * (2 * m + 1) + 12 := by
  apply refinement_cleared (k := 7) (r := 12) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_12]; decide

end Collatz.Research.RefinementAtlas.Batch035
