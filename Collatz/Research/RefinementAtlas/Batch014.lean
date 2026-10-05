import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 014. -/
namespace Collatz.Research.RefinementAtlas.Batch014
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 11). -/
theorem data_5_11 : oddCount 11 5 = 3 ∧
    acceleratedOrbit 5 11 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_11 : gap 5 11 = 5 ∧ 27 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_11 : threshold 5 11 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_11 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 11) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 11
  rw [data_5_11.1, data_5_11.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_11 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 11) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 11
  rw [data_5_11.1, data_5_11.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_11 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 11) < 32 * (2 * m) + 11 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 11 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_11] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 11) < 32 * (2 * m) + 11 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_11 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 11) < 32 * (2 * m + 1) + 11 := by
  apply refinement_cleared (k := 5) (r := 11) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_11]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 12). -/
theorem data_5_12 : oddCount 12 5 = 2 ∧
    acceleratedOrbit 5 12 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_12 : gap 5 12 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_12 : threshold 5 12 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_12 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 12) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 12
  rw [data_5_12.1, data_5_12.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_12 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 12) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 12
  rw [data_5_12.1, data_5_12.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_12 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 12) < 32 * (2 * m) + 12 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 12 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_12] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 12) < 32 * (2 * m) + 12 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_12 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 12) < 32 * (2 * m + 1) + 12 := by
  apply refinement_cleared (k := 5) (r := 12) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_12]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 13). -/
theorem data_5_13 : oddCount 13 5 = 2 ∧
    acceleratedOrbit 5 13 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_13 : gap 5 13 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_13 : threshold 5 13 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_13 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 13) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 13
  rw [data_5_13.1, data_5_13.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_13 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 13) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 13
  rw [data_5_13.1, data_5_13.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_13 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 13) < 32 * (2 * m) + 13 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 13 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_13] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 13) < 32 * (2 * m) + 13 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_13 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 13) < 32 * (2 * m + 1) + 13 := by
  apply refinement_cleared (k := 5) (r := 13) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_13]; decide

end Collatz.Research.RefinementAtlas.Batch014
