import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 066. -/
namespace Collatz.Research.RefinementAtlas.Batch066
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 6). -/
theorem data_8_6 : oddCount 6 8 = 3 ∧
    acceleratedOrbit 8 6 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_6 : gap 8 6 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_6 : threshold 8 6 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_6 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 6) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 6
  rw [data_8_6.1, data_8_6.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_6 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 6) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 6
  rw [data_8_6.1, data_8_6.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_6 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 6) < 256 * (2 * m) + 6 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 6 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_6] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 6) < 256 * (2 * m) + 6 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_6 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 6) < 256 * (2 * m + 1) + 6 := by
  apply refinement_cleared (k := 8) (r := 6) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_6]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 8). -/
theorem data_8_8 : oddCount 8 8 = 3 ∧
    acceleratedOrbit 8 8 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_8 : gap 8 8 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_8 : threshold 8 8 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_8 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 8) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 8
  rw [data_8_8.1, data_8_8.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_8 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 8) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 8
  rw [data_8_8.1, data_8_8.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_8 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 8) < 256 * (2 * m) + 8 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 8 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_8] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 8) < 256 * (2 * m) + 8 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_8 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 8) < 256 * (2 * m + 1) + 8 := by
  apply refinement_cleared (k := 8) (r := 8) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_8]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 10). -/
theorem data_8_10 : oddCount 10 8 = 3 ∧
    acceleratedOrbit 8 10 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_10 : gap 8 10 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_10 : threshold 8 10 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_10 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 10) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 10
  rw [data_8_10.1, data_8_10.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_10 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 10) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 10
  rw [data_8_10.1, data_8_10.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_10 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 10) < 256 * (2 * m) + 10 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 10 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_10] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 10) < 256 * (2 * m) + 10 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_10 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 10) < 256 * (2 * m + 1) + 10 := by
  apply refinement_cleared (k := 8) (r := 10) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_10]; decide

end Collatz.Research.RefinementAtlas.Batch066
