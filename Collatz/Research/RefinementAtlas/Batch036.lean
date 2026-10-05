import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 036. -/
namespace Collatz.Research.RefinementAtlas.Batch036
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 13). -/
theorem data_7_13 : oddCount 13 7 = 2 ∧
    acceleratedOrbit 7 13 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_13 : gap 7 13 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_13 : threshold 7 13 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_13 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 13) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 13
  rw [data_7_13.1, data_7_13.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_13 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 13) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 13
  rw [data_7_13.1, data_7_13.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_13 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 13) < 128 * (2 * m) + 13 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 13 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_13] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 13) < 128 * (2 * m) + 13 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_13 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 13) < 128 * (2 * m + 1) + 13 := by
  apply refinement_cleared (k := 7) (r := 13) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_13]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 14). -/
theorem data_7_14 : oddCount 14 7 = 4 ∧
    acceleratedOrbit 7 14 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_14 : gap 7 14 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_14 : threshold 7 14 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_14 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 14) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 14
  rw [data_7_14.1, data_7_14.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_14 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 14) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 14
  rw [data_7_14.1, data_7_14.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_14 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 14) < 128 * (2 * m) + 14 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 14 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_14] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 14) < 128 * (2 * m) + 14 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_14 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 14) < 128 * (2 * m + 1) + 14 := by
  apply refinement_cleared (k := 7) (r := 14) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_14]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 15). -/
theorem data_7_15 : oddCount 15 7 = 4 ∧
    acceleratedOrbit 7 15 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_15 : gap 7 15 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_15 : threshold 7 15 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_15 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 15) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 15
  rw [data_7_15.1, data_7_15.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_15 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 15) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 15
  rw [data_7_15.1, data_7_15.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_15 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 15) < 128 * (2 * m) + 15 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 15 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_15] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 15) < 128 * (2 * m) + 15 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_15 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 15) < 128 * (2 * m + 1) + 15 := by
  apply refinement_cleared (k := 7) (r := 15) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_15]; decide

end Collatz.Research.RefinementAtlas.Batch036
