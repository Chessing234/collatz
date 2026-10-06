import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 294. -/
namespace Collatz.Research.RefinementAtlas.Batch294
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 120). -/
theorem data_10_120 : oddCount 120 10 = 4 ∧
    acceleratedOrbit 10 120 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_120 : gap 10 120 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_120 : threshold 10 120 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_120 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 120) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 120
  rw [data_10_120.1, data_10_120.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_120 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 120) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 120
  rw [data_10_120.1, data_10_120.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_120 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 120) < 1024 * (2 * m) + 120 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 120 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_120] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 120) < 1024 * (2 * m) + 120 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_120 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 120) < 1024 * (2 * m + 1) + 120 := by
  apply refinement_cleared (k := 10) (r := 120) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_120]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 122). -/
theorem data_10_122 : oddCount 122 10 = 4 ∧
    acceleratedOrbit 10 122 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_122 : gap 10 122 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_122 : threshold 10 122 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_122 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 122) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 122
  rw [data_10_122.1, data_10_122.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_122 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 122) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 122
  rw [data_10_122.1, data_10_122.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_122 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 122) < 1024 * (2 * m) + 122 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 122 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_122] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 122) < 1024 * (2 * m) + 122 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_122 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 122) < 1024 * (2 * m + 1) + 122 := by
  apply refinement_cleared (k := 10) (r := 122) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_122]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 123). -/
theorem data_10_123 : oddCount 123 10 = 6 ∧
    acceleratedOrbit 10 123 = 89 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_123 : gap 10 123 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_123 : threshold 10 123 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_123 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 123) = 729 * (2 * m) + 89 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 123
  rw [data_10_123.1, data_10_123.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_123 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 123) = 729 * (2 * m + 1) + 89 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 123
  rw [data_10_123.1, data_10_123.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_123 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 123) < 1024 * (2 * m) + 123 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 123 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_123] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 123) < 1024 * (2 * m) + 123 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_123 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 123) < 1024 * (2 * m + 1) + 123 := by
  apply refinement_cleared (k := 10) (r := 123) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_123]; decide

end Collatz.Research.RefinementAtlas.Batch294
