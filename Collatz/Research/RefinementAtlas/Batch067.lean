import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 067. -/
namespace Collatz.Research.RefinementAtlas.Batch067
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 11). -/
theorem data_8_11 : oddCount 11 8 = 4 ∧
    acceleratedOrbit 8 11 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_11 : gap 8 11 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_11 : threshold 8 11 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_11 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 11) = 81 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 11
  rw [data_8_11.1, data_8_11.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_11 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 11) = 81 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 11
  rw [data_8_11.1, data_8_11.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_11 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 11) < 256 * (2 * m) + 11 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 11 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_11] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 11) < 256 * (2 * m) + 11 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_11 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 11) < 256 * (2 * m + 1) + 11 := by
  apply refinement_cleared (k := 8) (r := 11) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_11]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 12). -/
theorem data_8_12 : oddCount 12 8 = 3 ∧
    acceleratedOrbit 8 12 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_12 : gap 8 12 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_12 : threshold 8 12 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_12 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 12) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 12
  rw [data_8_12.1, data_8_12.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_12 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 12) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 12
  rw [data_8_12.1, data_8_12.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_12 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 12) < 256 * (2 * m) + 12 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 12 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_12] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 12) < 256 * (2 * m) + 12 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_12 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 12) < 256 * (2 * m + 1) + 12 := by
  apply refinement_cleared (k := 8) (r := 12) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_12]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 13). -/
theorem data_8_13 : oddCount 13 8 = 3 ∧
    acceleratedOrbit 8 13 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_13 : gap 8 13 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_13 : threshold 8 13 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_13 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 13) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 13
  rw [data_8_13.1, data_8_13.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_13 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 13) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 13
  rw [data_8_13.1, data_8_13.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_13 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 13) < 256 * (2 * m) + 13 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 13 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_13] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 13) < 256 * (2 * m) + 13 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_13 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 13) < 256 * (2 * m + 1) + 13 := by
  apply refinement_cleared (k := 8) (r := 13) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_13]; decide

end Collatz.Research.RefinementAtlas.Batch067
