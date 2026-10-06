import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 010. -/
namespace Collatz.Research.RefinementAtlas.Batch010
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (4, 6). -/
theorem data_4_6 : oddCount 6 4 = 2 ∧
    acceleratedOrbit 4 6 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_6 : gap 4 6 = 7 ∧ 9 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_6 : threshold 4 6 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_6 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 6) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 6
  rw [data_4_6.1, data_4_6.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_6 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 6) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 6
  rw [data_4_6.1, data_4_6.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_6 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 6) < 16 * (2 * m) + 6 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 6 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_6] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 6) < 16 * (2 * m) + 6 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_6 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 6) < 16 * (2 * m + 1) + 6 := by
  apply refinement_cleared (k := 4) (r := 6) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_6]; decide

/-- Kernel-evaluated parity count and endpoint for (4, 8). -/
theorem data_4_8 : oddCount 8 4 = 1 ∧
    acceleratedOrbit 4 8 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_8 : gap 4 8 = 13 ∧ 3 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_8 : threshold 4 8 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_8 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 8) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 8
  rw [data_4_8.1, data_4_8.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_8 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 8) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 8
  rw [data_4_8.1, data_4_8.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_8 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 8) < 16 * (2 * m) + 8 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 8 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_8] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 8) < 16 * (2 * m) + 8 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_8 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 8) < 16 * (2 * m + 1) + 8 := by
  apply refinement_cleared (k := 4) (r := 8) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_8]; decide

/-- Kernel-evaluated parity count and endpoint for (4, 10). -/
theorem data_4_10 : oddCount 10 4 = 1 ∧
    acceleratedOrbit 4 10 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_4_10 : gap 4 10 = 13 ∧ 3 < 16 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_4_10 : threshold 4 10 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_4_10 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 10) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m) 10
  rw [data_4_10.1, data_4_10.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_4_10 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 10) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 4 (2 * m + 1) 10
  rw [data_4_10.1, data_4_10.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_4_10 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m) + 10) < 16 * (2 * m) + 10 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 10 4 < 2 ^ 4 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_4_10] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 4 (16 * (2 * m) + 10) < 16 * (2 * m) + 10 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_4_10 (m : Nat) :
    acceleratedOrbit 4 (16 * (2 * m + 1) + 10) < 16 * (2 * m + 1) + 10 := by
  apply refinement_cleared (k := 4) (r := 10) (s := 2) (q := 1)
  · decide
  · rw [cutoff_4_10]; decide

end Collatz.Research.RefinementAtlas.Batch010
