import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 072. -/
namespace Collatz.Research.RefinementAtlas.Batch072
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 30). -/
theorem data_8_30 : oddCount 30 8 = 4 ∧
    acceleratedOrbit 8 30 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_30 : gap 8 30 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_30 : threshold 8 30 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_30 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 30) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 30
  rw [data_8_30.1, data_8_30.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_30 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 30) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 30
  rw [data_8_30.1, data_8_30.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_30 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 30) < 256 * (2 * m) + 30 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 30 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_30] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 30) < 256 * (2 * m) + 30 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_30 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 30) < 256 * (2 * m + 1) + 30 := by
  apply refinement_cleared (k := 8) (r := 30) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_30]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 32). -/
theorem data_8_32 : oddCount 32 8 = 2 ∧
    acceleratedOrbit 8 32 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_32 : gap 8 32 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_32 : threshold 8 32 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_32 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 32) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 32
  rw [data_8_32.1, data_8_32.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_32 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 32) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 32
  rw [data_8_32.1, data_8_32.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_32 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 32) < 256 * (2 * m) + 32 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 32 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_32] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 32) < 256 * (2 * m) + 32 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_32 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 32) < 256 * (2 * m + 1) + 32 := by
  apply refinement_cleared (k := 8) (r := 32) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_32]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 33). -/
theorem data_8_33 : oddCount 33 8 = 4 ∧
    acceleratedOrbit 8 33 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_33 : gap 8 33 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_33 : threshold 8 33 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_33 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 33) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 33
  rw [data_8_33.1, data_8_33.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_33 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 33) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 33
  rw [data_8_33.1, data_8_33.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_33 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 33) < 256 * (2 * m) + 33 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 33 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_33] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 33) < 256 * (2 * m) + 33 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_33 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 33) < 256 * (2 * m + 1) + 33 := by
  apply refinement_cleared (k := 8) (r := 33) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_33]; decide

end Collatz.Research.RefinementAtlas.Batch072
