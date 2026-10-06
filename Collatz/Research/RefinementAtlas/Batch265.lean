import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 265. -/
namespace Collatz.Research.RefinementAtlas.Batch265
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 12). -/
theorem data_10_12 : oddCount 12 10 = 4 ∧
    acceleratedOrbit 10 12 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_12 : gap 10 12 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_12 : threshold 10 12 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_12 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 12) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 12
  rw [data_10_12.1, data_10_12.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_12 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 12) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 12
  rw [data_10_12.1, data_10_12.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_12 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 12) < 1024 * (2 * m) + 12 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 12 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_12] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 12) < 1024 * (2 * m) + 12 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_12 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 12) < 1024 * (2 * m + 1) + 12 := by
  apply refinement_cleared (k := 10) (r := 12) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_12]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 13). -/
theorem data_10_13 : oddCount 13 10 = 4 ∧
    acceleratedOrbit 10 13 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_13 : gap 10 13 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_13 : threshold 10 13 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_13 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 13) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 13
  rw [data_10_13.1, data_10_13.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_13 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 13) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 13
  rw [data_10_13.1, data_10_13.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_13 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 13) < 1024 * (2 * m) + 13 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 13 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_13] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 13) < 1024 * (2 * m) + 13 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_13 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 13) < 1024 * (2 * m + 1) + 13 := by
  apply refinement_cleared (k := 10) (r := 13) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_13]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 14). -/
theorem data_10_14 : oddCount 14 10 = 5 ∧
    acceleratedOrbit 10 14 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_14 : gap 10 14 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_14 : threshold 10 14 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_14 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 14) = 243 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 14
  rw [data_10_14.1, data_10_14.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_14 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 14) = 243 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 14
  rw [data_10_14.1, data_10_14.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_14 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 14) < 1024 * (2 * m) + 14 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 14 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_14] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 14) < 1024 * (2 * m) + 14 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_14 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 14) < 1024 * (2 * m + 1) + 14 := by
  apply refinement_cleared (k := 10) (r := 14) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_14]; decide

end Collatz.Research.RefinementAtlas.Batch265
