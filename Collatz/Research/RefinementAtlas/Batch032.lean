import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 032. -/
namespace Collatz.Research.RefinementAtlas.Batch032
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 56). -/
theorem data_6_56 : oddCount 56 6 = 3 ∧
    acceleratedOrbit 6 56 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_56 : gap 6 56 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_56 : threshold 6 56 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_56 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 56) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 56
  rw [data_6_56.1, data_6_56.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_56 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 56) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 56
  rw [data_6_56.1, data_6_56.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_56 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 56) < 64 * (2 * m) + 56 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 56 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_56] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 56) < 64 * (2 * m) + 56 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_56 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 56) < 64 * (2 * m + 1) + 56 := by
  apply refinement_cleared (k := 6) (r := 56) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_56]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 58). -/
theorem data_6_58 : oddCount 58 6 = 3 ∧
    acceleratedOrbit 6 58 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_58 : gap 6 58 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_58 : threshold 6 58 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_58 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 58) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 58
  rw [data_6_58.1, data_6_58.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_58 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 58) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 58
  rw [data_6_58.1, data_6_58.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_58 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 58) < 64 * (2 * m) + 58 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 58 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_58] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 58) < 64 * (2 * m) + 58 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_58 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 58) < 64 * (2 * m + 1) + 58 := by
  apply refinement_cleared (k := 6) (r := 58) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_58]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 2). -/
theorem data_7_2 : oddCount 2 7 = 3 ∧
    acceleratedOrbit 7 2 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_2 : gap 7 2 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_2 : threshold 7 2 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_2 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 2) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 2
  rw [data_7_2.1, data_7_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_2 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 2) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 2
  rw [data_7_2.1, data_7_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_2 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 2) < 128 * (2 * m) + 2 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 2 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 2) < 128 * (2 * m) + 2 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_2 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 2) < 128 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 7) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_2]; decide

end Collatz.Research.RefinementAtlas.Batch032
