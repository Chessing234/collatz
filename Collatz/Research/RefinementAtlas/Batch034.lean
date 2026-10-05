import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 034. -/
namespace Collatz.Research.RefinementAtlas.Batch034
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 6). -/
theorem data_7_6 : oddCount 6 7 = 3 ∧
    acceleratedOrbit 7 6 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_6 : gap 7 6 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_6 : threshold 7 6 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_6 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 6) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 6
  rw [data_7_6.1, data_7_6.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_6 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 6) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 6
  rw [data_7_6.1, data_7_6.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_6 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 6) < 128 * (2 * m) + 6 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 6 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_6] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 6) < 128 * (2 * m) + 6 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_6 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 6) < 128 * (2 * m + 1) + 6 := by
  apply refinement_cleared (k := 7) (r := 6) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_6]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 7). -/
theorem data_7_7 : oddCount 7 7 = 4 ∧
    acceleratedOrbit 7 7 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_7 : gap 7 7 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_7 : threshold 7 7 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_7 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 7) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 7
  rw [data_7_7.1, data_7_7.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_7 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 7) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 7
  rw [data_7_7.1, data_7_7.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_7 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 7) < 128 * (2 * m) + 7 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 7 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_7] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 7) < 128 * (2 * m) + 7 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_7 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 7) < 128 * (2 * m + 1) + 7 := by
  apply refinement_cleared (k := 7) (r := 7) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_7]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 8). -/
theorem data_7_8 : oddCount 8 7 = 2 ∧
    acceleratedOrbit 7 8 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_8 : gap 7 8 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_8 : threshold 7 8 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_8 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 8) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 8
  rw [data_7_8.1, data_7_8.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_8 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 8) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 8
  rw [data_7_8.1, data_7_8.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_8 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 8) < 128 * (2 * m) + 8 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 8 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_8] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 8) < 128 * (2 * m) + 8 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_8 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 8) < 128 * (2 * m + 1) + 8 := by
  apply refinement_cleared (k := 7) (r := 8) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_8]; decide

end Collatz.Research.RefinementAtlas.Batch034
