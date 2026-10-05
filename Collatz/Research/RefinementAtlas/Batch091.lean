import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 091. -/
namespace Collatz.Research.RefinementAtlas.Batch091
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 98). -/
theorem data_8_98 : oddCount 98 8 = 3 ∧
    acceleratedOrbit 8 98 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_98 : gap 8 98 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_98 : threshold 8 98 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_98 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 98) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 98
  rw [data_8_98.1, data_8_98.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_98 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 98) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 98
  rw [data_8_98.1, data_8_98.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_98 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 98) < 256 * (2 * m) + 98 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 98 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_98] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 98) < 256 * (2 * m) + 98 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_98 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 98) < 256 * (2 * m + 1) + 98 := by
  apply refinement_cleared (k := 8) (r := 98) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_98]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 99). -/
theorem data_8_99 : oddCount 99 8 = 3 ∧
    acceleratedOrbit 8 99 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_99 : gap 8 99 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_99 : threshold 8 99 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_99 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 99) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 99
  rw [data_8_99.1, data_8_99.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_99 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 99) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 99
  rw [data_8_99.1, data_8_99.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_99 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 99) < 256 * (2 * m) + 99 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 99 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_99] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 99) < 256 * (2 * m) + 99 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_99 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 99) < 256 * (2 * m + 1) + 99 := by
  apply refinement_cleared (k := 8) (r := 99) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_99]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 100). -/
theorem data_8_100 : oddCount 100 8 = 3 ∧
    acceleratedOrbit 8 100 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_100 : gap 8 100 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_100 : threshold 8 100 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_100 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 100) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 100
  rw [data_8_100.1, data_8_100.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_100 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 100) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 100
  rw [data_8_100.1, data_8_100.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_100 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 100) < 256 * (2 * m) + 100 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 100 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_100] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 100) < 256 * (2 * m) + 100 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_100 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 100) < 256 * (2 * m + 1) + 100 := by
  apply refinement_cleared (k := 8) (r := 100) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_100]; decide

end Collatz.Research.RefinementAtlas.Batch091
