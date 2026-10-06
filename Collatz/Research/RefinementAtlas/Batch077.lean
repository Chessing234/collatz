import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 077. -/
namespace Collatz.Research.RefinementAtlas.Batch077
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 48). -/
theorem data_8_48 : oddCount 48 8 = 2 ∧
    acceleratedOrbit 8 48 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_48 : gap 8 48 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_48 : threshold 8 48 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_48 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 48) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 48
  rw [data_8_48.1, data_8_48.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_48 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 48) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 48
  rw [data_8_48.1, data_8_48.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_48 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 48) < 256 * (2 * m) + 48 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 48 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_48] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 48) < 256 * (2 * m) + 48 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_48 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 48) < 256 * (2 * m + 1) + 48 := by
  apply refinement_cleared (k := 8) (r := 48) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_48]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 49). -/
theorem data_8_49 : oddCount 49 8 = 4 ∧
    acceleratedOrbit 8 49 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_49 : gap 8 49 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_49 : threshold 8 49 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_49 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 49) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 49
  rw [data_8_49.1, data_8_49.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_49 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 49) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 49
  rw [data_8_49.1, data_8_49.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_49 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 49) < 256 * (2 * m) + 49 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 49 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_49] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 49) < 256 * (2 * m) + 49 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_49 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 49) < 256 * (2 * m + 1) + 49 := by
  apply refinement_cleared (k := 8) (r := 49) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_49]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 50). -/
theorem data_8_50 : oddCount 50 8 = 4 ∧
    acceleratedOrbit 8 50 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_50 : gap 8 50 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_50 : threshold 8 50 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_50 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 50) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 50
  rw [data_8_50.1, data_8_50.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_50 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 50) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 50
  rw [data_8_50.1, data_8_50.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_50 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 50) < 256 * (2 * m) + 50 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 50 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_50] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 50) < 256 * (2 * m) + 50 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_50 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 50) < 256 * (2 * m + 1) + 50 := by
  apply refinement_cleared (k := 8) (r := 50) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_50]; decide

end Collatz.Research.RefinementAtlas.Batch077
