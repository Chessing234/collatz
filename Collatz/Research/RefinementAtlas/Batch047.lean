import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 047. -/
namespace Collatz.Research.RefinementAtlas.Batch047
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 51). -/
theorem data_7_51 : oddCount 51 7 = 3 ∧
    acceleratedOrbit 7 51 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_51 : gap 7 51 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_51 : threshold 7 51 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_51 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 51) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 51
  rw [data_7_51.1, data_7_51.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_51 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 51) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 51
  rw [data_7_51.1, data_7_51.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_51 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 51) < 128 * (2 * m) + 51 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 51 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_51] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 51) < 128 * (2 * m) + 51 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_51 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 51) < 128 * (2 * m + 1) + 51 := by
  apply refinement_cleared (k := 7) (r := 51) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_51]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 52). -/
theorem data_7_52 : oddCount 52 7 = 2 ∧
    acceleratedOrbit 7 52 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_52 : gap 7 52 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_52 : threshold 7 52 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_52 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 52) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 52
  rw [data_7_52.1, data_7_52.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_52 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 52) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 52
  rw [data_7_52.1, data_7_52.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_52 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 52) < 128 * (2 * m) + 52 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 52 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_52] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 52) < 128 * (2 * m) + 52 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_52 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 52) < 128 * (2 * m + 1) + 52 := by
  apply refinement_cleared (k := 7) (r := 52) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_52]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 53). -/
theorem data_7_53 : oddCount 53 7 = 2 ∧
    acceleratedOrbit 7 53 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_53 : gap 7 53 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_53 : threshold 7 53 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_53 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 53) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 53
  rw [data_7_53.1, data_7_53.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_53 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 53) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 53
  rw [data_7_53.1, data_7_53.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_53 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 53) < 128 * (2 * m) + 53 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 53 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_53] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 53) < 128 * (2 * m) + 53 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_53 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 53) < 128 * (2 * m + 1) + 53 := by
  apply refinement_cleared (k := 7) (r := 53) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_53]; decide

end Collatz.Research.RefinementAtlas.Batch047
