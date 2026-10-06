import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 138. -/
namespace Collatz.Research.RefinementAtlas.Batch138
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 10). -/
theorem data_9_10 : oddCount 10 9 = 3 ∧
    acceleratedOrbit 9 10 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_10 : gap 9 10 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_10 : threshold 9 10 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_10 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 10) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 10
  rw [data_9_10.1, data_9_10.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_10 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 10) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 10
  rw [data_9_10.1, data_9_10.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_10 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 10) < 512 * (2 * m) + 10 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 10 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_10] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 10) < 512 * (2 * m) + 10 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_10 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 10) < 512 * (2 * m + 1) + 10 := by
  apply refinement_cleared (k := 9) (r := 10) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_10]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 11). -/
theorem data_9_11 : oddCount 11 9 = 4 ∧
    acceleratedOrbit 9 11 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_11 : gap 9 11 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_11 : threshold 9 11 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_11 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 11) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 11
  rw [data_9_11.1, data_9_11.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_11 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 11) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 11
  rw [data_9_11.1, data_9_11.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_11 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 11) < 512 * (2 * m) + 11 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 11 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_11] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 11) < 512 * (2 * m) + 11 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_11 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 11) < 512 * (2 * m + 1) + 11 := by
  apply refinement_cleared (k := 9) (r := 11) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_11]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 12). -/
theorem data_9_12 : oddCount 12 9 = 3 ∧
    acceleratedOrbit 9 12 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_12 : gap 9 12 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_12 : threshold 9 12 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_12 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 12) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 12
  rw [data_9_12.1, data_9_12.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_12 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 12) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 12
  rw [data_9_12.1, data_9_12.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_12 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 12) < 512 * (2 * m) + 12 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 12 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_12] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 12) < 512 * (2 * m) + 12 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_12 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 12) < 512 * (2 * m + 1) + 12 := by
  apply refinement_cleared (k := 9) (r := 12) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_12]; decide

end Collatz.Research.RefinementAtlas.Batch138
