import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 068. -/
namespace Collatz.Research.RefinementAtlas.Batch068
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 14). -/
theorem data_8_14 : oddCount 14 8 = 4 ∧
    acceleratedOrbit 8 14 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_14 : gap 8 14 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_14 : threshold 8 14 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_14 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 14) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 14
  rw [data_8_14.1, data_8_14.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_14 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 14) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 14
  rw [data_8_14.1, data_8_14.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_14 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 14) < 256 * (2 * m) + 14 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 14 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_14] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 14) < 256 * (2 * m) + 14 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_14 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 14) < 256 * (2 * m + 1) + 14 := by
  apply refinement_cleared (k := 8) (r := 14) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_14]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 15). -/
theorem data_8_15 : oddCount 15 8 = 4 ∧
    acceleratedOrbit 8 15 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_15 : gap 8 15 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_15 : threshold 8 15 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_15 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 15) = 81 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 15
  rw [data_8_15.1, data_8_15.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_15 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 15) = 81 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 15
  rw [data_8_15.1, data_8_15.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_15 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 15) < 256 * (2 * m) + 15 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 15 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_15] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 15) < 256 * (2 * m) + 15 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_15 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 15) < 256 * (2 * m + 1) + 15 := by
  apply refinement_cleared (k := 8) (r := 15) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_15]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 16). -/
theorem data_8_16 : oddCount 16 8 = 2 ∧
    acceleratedOrbit 8 16 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_16 : gap 8 16 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_16 : threshold 8 16 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_16 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 16) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 16
  rw [data_8_16.1, data_8_16.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_16 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 16) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 16
  rw [data_8_16.1, data_8_16.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_16 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 16) < 256 * (2 * m) + 16 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 16 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_16] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 16) < 256 * (2 * m) + 16 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_16 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 16) < 256 * (2 * m + 1) + 16 := by
  apply refinement_cleared (k := 8) (r := 16) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_16]; decide

end Collatz.Research.RefinementAtlas.Batch068
