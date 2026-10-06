import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 300. -/
namespace Collatz.Research.RefinementAtlas.Batch300
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 141). -/
theorem data_10_141 : oddCount 141 10 = 3 ∧
    acceleratedOrbit 10 141 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_141 : gap 10 141 = 997 ∧ 27 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_141 : threshold 10 141 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_141 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 141) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 141
  rw [data_10_141.1, data_10_141.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_141 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 141) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 141
  rw [data_10_141.1, data_10_141.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_141 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 141) < 1024 * (2 * m) + 141 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 141 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_141] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 141) < 1024 * (2 * m) + 141 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_141 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 141) < 1024 * (2 * m + 1) + 141 := by
  apply refinement_cleared (k := 10) (r := 141) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_141]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 142). -/
theorem data_10_142 : oddCount 142 10 = 6 ∧
    acceleratedOrbit 10 142 = 103 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_142 : gap 10 142 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_142 : threshold 10 142 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_142 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 142) = 729 * (2 * m) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 142
  rw [data_10_142.1, data_10_142.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_142 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 142) = 729 * (2 * m + 1) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 142
  rw [data_10_142.1, data_10_142.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_142 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 142) < 1024 * (2 * m) + 142 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 142 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_142] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 142) < 1024 * (2 * m) + 142 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_142 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 142) < 1024 * (2 * m + 1) + 142 := by
  apply refinement_cleared (k := 10) (r := 142) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_142]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 143). -/
theorem data_10_143 : oddCount 143 10 = 6 ∧
    acceleratedOrbit 10 143 = 103 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_143 : gap 10 143 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_143 : threshold 10 143 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_143 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 143) = 729 * (2 * m) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 143
  rw [data_10_143.1, data_10_143.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_143 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 143) = 729 * (2 * m + 1) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 143
  rw [data_10_143.1, data_10_143.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_143 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 143) < 1024 * (2 * m) + 143 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 143 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_143] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 143) < 1024 * (2 * m) + 143 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_143 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 143) < 1024 * (2 * m + 1) + 143 := by
  apply refinement_cleared (k := 10) (r := 143) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_143]; decide

end Collatz.Research.RefinementAtlas.Batch300
