import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 048. -/
namespace Collatz.Research.RefinementAtlas.Batch048
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 56). -/
theorem data_7_56 : oddCount 56 7 = 3 ∧
    acceleratedOrbit 7 56 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_56 : gap 7 56 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_56 : threshold 7 56 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_56 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 56) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 56
  rw [data_7_56.1, data_7_56.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_56 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 56) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 56
  rw [data_7_56.1, data_7_56.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_56 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 56) < 128 * (2 * m) + 56 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 56 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_56] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 56) < 128 * (2 * m) + 56 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_56 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 56) < 128 * (2 * m + 1) + 56 := by
  apply refinement_cleared (k := 7) (r := 56) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_56]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 57). -/
theorem data_7_57 : oddCount 57 7 = 4 ∧
    acceleratedOrbit 7 57 = 37 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_57 : gap 7 57 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_57 : threshold 7 57 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_57 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 57) = 81 * (2 * m) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 57
  rw [data_7_57.1, data_7_57.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_57 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 57) = 81 * (2 * m + 1) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 57
  rw [data_7_57.1, data_7_57.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_57 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 57) < 128 * (2 * m) + 57 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 57 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_57] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 57) < 128 * (2 * m) + 57 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_57 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 57) < 128 * (2 * m + 1) + 57 := by
  apply refinement_cleared (k := 7) (r := 57) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_57]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 58). -/
theorem data_7_58 : oddCount 58 7 = 3 ∧
    acceleratedOrbit 7 58 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_58 : gap 7 58 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_58 : threshold 7 58 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_58 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 58) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 58
  rw [data_7_58.1, data_7_58.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_58 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 58) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 58
  rw [data_7_58.1, data_7_58.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_58 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 58) < 128 * (2 * m) + 58 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 58 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_58] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 58) < 128 * (2 * m) + 58 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_58 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 58) < 128 * (2 * m + 1) + 58 := by
  apply refinement_cleared (k := 7) (r := 58) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_58]; decide

end Collatz.Research.RefinementAtlas.Batch048
