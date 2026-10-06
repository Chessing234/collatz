import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 263. -/
namespace Collatz.Research.RefinementAtlas.Batch263
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 6). -/
theorem data_10_6 : oddCount 6 10 = 4 ∧
    acceleratedOrbit 10 6 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_6 : gap 10 6 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_6 : threshold 10 6 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_6 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 6) = 81 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 6
  rw [data_10_6.1, data_10_6.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_6 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 6) = 81 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 6
  rw [data_10_6.1, data_10_6.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_6 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 6) < 1024 * (2 * m) + 6 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 6 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_6] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 6) < 1024 * (2 * m) + 6 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_6 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 6) < 1024 * (2 * m + 1) + 6 := by
  apply refinement_cleared (k := 10) (r := 6) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_6]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 7). -/
theorem data_10_7 : oddCount 7 10 = 5 ∧
    acceleratedOrbit 10 7 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_7 : gap 10 7 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_7 : threshold 10 7 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_7 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 7) = 243 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 7
  rw [data_10_7.1, data_10_7.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_7 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 7) = 243 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 7
  rw [data_10_7.1, data_10_7.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_7 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 7) < 1024 * (2 * m) + 7 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 7 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_7] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 7) < 1024 * (2 * m) + 7 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_7 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 7) < 1024 * (2 * m + 1) + 7 := by
  apply refinement_cleared (k := 10) (r := 7) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_7]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 8). -/
theorem data_10_8 : oddCount 8 10 = 4 ∧
    acceleratedOrbit 10 8 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_8 : gap 10 8 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_8 : threshold 10 8 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_8 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 8) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 8
  rw [data_10_8.1, data_10_8.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_8 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 8) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 8
  rw [data_10_8.1, data_10_8.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_8 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 8) < 1024 * (2 * m) + 8 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 8 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_8] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 8) < 1024 * (2 * m) + 8 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_8 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 8) < 1024 * (2 * m + 1) + 8 := by
  apply refinement_cleared (k := 10) (r := 8) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_8]; decide

end Collatz.Research.RefinementAtlas.Batch263
