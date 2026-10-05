import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 264. -/
namespace Collatz.Research.RefinementAtlas.Batch264
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 9). -/
theorem data_10_9 : oddCount 9 10 = 6 ∧
    acceleratedOrbit 10 9 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_9 : gap 10 9 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_9 : threshold 10 9 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_9 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 9) = 729 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 9
  rw [data_10_9.1, data_10_9.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_9 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 9) = 729 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 9
  rw [data_10_9.1, data_10_9.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_9 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 9) < 1024 * (2 * m) + 9 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 9 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_9] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 9) < 1024 * (2 * m) + 9 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_9 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 9) < 1024 * (2 * m + 1) + 9 := by
  apply refinement_cleared (k := 10) (r := 9) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_9]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 10). -/
theorem data_10_10 : oddCount 10 10 = 4 ∧
    acceleratedOrbit 10 10 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_10 : gap 10 10 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_10 : threshold 10 10 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_10 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 10) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 10
  rw [data_10_10.1, data_10_10.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_10 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 10) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 10
  rw [data_10_10.1, data_10_10.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_10 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 10) < 1024 * (2 * m) + 10 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 10 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_10] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 10) < 1024 * (2 * m) + 10 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_10 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 10) < 1024 * (2 * m + 1) + 10 := by
  apply refinement_cleared (k := 10) (r := 10) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_10]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 11). -/
theorem data_10_11 : oddCount 11 10 = 4 ∧
    acceleratedOrbit 10 11 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_11 : gap 10 11 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_11 : threshold 10 11 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_11 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 11) = 81 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 11
  rw [data_10_11.1, data_10_11.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_11 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 11) = 81 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 11
  rw [data_10_11.1, data_10_11.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_11 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 11) < 1024 * (2 * m) + 11 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 11 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_11] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 11) < 1024 * (2 * m) + 11 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_11 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 11) < 1024 * (2 * m + 1) + 11 := by
  apply refinement_cleared (k := 10) (r := 11) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_11]; decide

end Collatz.Research.RefinementAtlas.Batch264
