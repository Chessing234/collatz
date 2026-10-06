import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 097. -/
namespace Collatz.Research.RefinementAtlas.Batch097
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 118). -/
theorem data_8_118 : oddCount 118 8 = 4 ∧
    acceleratedOrbit 8 118 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_118 : gap 8 118 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_118 : threshold 8 118 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_118 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 118) = 81 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 118
  rw [data_8_118.1, data_8_118.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_118 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 118) = 81 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 118
  rw [data_8_118.1, data_8_118.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_118 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 118) < 256 * (2 * m) + 118 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 118 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_118] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 118) < 256 * (2 * m) + 118 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_118 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 118) < 256 * (2 * m + 1) + 118 := by
  apply refinement_cleared (k := 8) (r := 118) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_118]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 119). -/
theorem data_8_119 : oddCount 119 8 = 4 ∧
    acceleratedOrbit 8 119 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_119 : gap 8 119 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_119 : threshold 8 119 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_119 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 119) = 81 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 119
  rw [data_8_119.1, data_8_119.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_119 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 119) = 81 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 119
  rw [data_8_119.1, data_8_119.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_119 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 119) < 256 * (2 * m) + 119 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 119 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_119] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 119) < 256 * (2 * m) + 119 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_119 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 119) < 256 * (2 * m + 1) + 119 := by
  apply refinement_cleared (k := 8) (r := 119) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_119]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 120). -/
theorem data_8_120 : oddCount 120 8 = 4 ∧
    acceleratedOrbit 8 120 = 40 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_120 : gap 8 120 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_120 : threshold 8 120 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_120 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 120) = 81 * (2 * m) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 120
  rw [data_8_120.1, data_8_120.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_120 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 120) = 81 * (2 * m + 1) + 40 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 120
  rw [data_8_120.1, data_8_120.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_120 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 120) < 256 * (2 * m) + 120 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 120 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_120] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 120) < 256 * (2 * m) + 120 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_120 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 120) < 256 * (2 * m + 1) + 120 := by
  apply refinement_cleared (k := 8) (r := 120) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_120]; decide

end Collatz.Research.RefinementAtlas.Batch097
