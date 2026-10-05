import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 046. -/
namespace Collatz.Research.RefinementAtlas.Batch046
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 48). -/
theorem data_7_48 : oddCount 48 7 = 2 ∧
    acceleratedOrbit 7 48 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_48 : gap 7 48 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_48 : threshold 7 48 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_48 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 48) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 48
  rw [data_7_48.1, data_7_48.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_48 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 48) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 48
  rw [data_7_48.1, data_7_48.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_48 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 48) < 128 * (2 * m) + 48 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 48 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_48] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 48) < 128 * (2 * m) + 48 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_48 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 48) < 128 * (2 * m + 1) + 48 := by
  apply refinement_cleared (k := 7) (r := 48) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_48]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 49). -/
theorem data_7_49 : oddCount 49 7 = 3 ∧
    acceleratedOrbit 7 49 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_49 : gap 7 49 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_49 : threshold 7 49 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_49 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 49) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 49
  rw [data_7_49.1, data_7_49.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_49 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 49) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 49
  rw [data_7_49.1, data_7_49.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_49 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 49) < 128 * (2 * m) + 49 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 49 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_49] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 49) < 128 * (2 * m) + 49 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_49 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 49) < 128 * (2 * m + 1) + 49 := by
  apply refinement_cleared (k := 7) (r := 49) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_49]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 50). -/
theorem data_7_50 : oddCount 50 7 = 3 ∧
    acceleratedOrbit 7 50 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_50 : gap 7 50 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_50 : threshold 7 50 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_50 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 50) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 50
  rw [data_7_50.1, data_7_50.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_50 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 50) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 50
  rw [data_7_50.1, data_7_50.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_50 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 50) < 128 * (2 * m) + 50 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 50 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_50] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 50) < 128 * (2 * m) + 50 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_50 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 50) < 128 * (2 * m + 1) + 50 := by
  apply refinement_cleared (k := 7) (r := 50) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_50]; decide

end Collatz.Research.RefinementAtlas.Batch046
