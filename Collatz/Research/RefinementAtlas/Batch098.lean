import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 098. -/
namespace Collatz.Research.RefinementAtlas.Batch098
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 122). -/
theorem data_8_122 : oddCount 122 8 = 4 ∧
    acceleratedOrbit 8 122 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_122 : gap 8 122 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_122 : threshold 8 122 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_122 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 122) = 81 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 122
  rw [data_8_122.1, data_8_122.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_122 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 122) = 81 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 122
  rw [data_8_122.1, data_8_122.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_122 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 122) < 256 * (2 * m) + 122 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 122 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_122] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 122) < 256 * (2 * m) + 122 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_122 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 122) < 256 * (2 * m + 1) + 122 := by
  apply refinement_cleared (k := 8) (r := 122) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_122]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 123). -/
theorem data_8_123 : oddCount 123 8 = 5 ∧
    acceleratedOrbit 8 123 = 118 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_123 : gap 8 123 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_123 : threshold 8 123 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_123 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 123) = 243 * (2 * m) + 118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 123
  rw [data_8_123.1, data_8_123.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_123 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 123) = 243 * (2 * m + 1) + 118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 123
  rw [data_8_123.1, data_8_123.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_123 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 123) < 256 * (2 * m) + 123 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 123 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_123] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 123) < 256 * (2 * m) + 123 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_123 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 123) < 256 * (2 * m + 1) + 123 := by
  apply refinement_cleared (k := 8) (r := 123) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_123]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 124). -/
theorem data_8_124 : oddCount 124 8 = 5 ∧
    acceleratedOrbit 8 124 = 121 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_124 : gap 8 124 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_124 : threshold 8 124 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_124 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 124) = 243 * (2 * m) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 124
  rw [data_8_124.1, data_8_124.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_124 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 124) = 243 * (2 * m + 1) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 124
  rw [data_8_124.1, data_8_124.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_124 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 124) < 256 * (2 * m) + 124 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 124 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_124] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 124) < 256 * (2 * m) + 124 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_124 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 124) < 256 * (2 * m + 1) + 124 := by
  apply refinement_cleared (k := 8) (r := 124) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_124]; decide

end Collatz.Research.RefinementAtlas.Batch098
