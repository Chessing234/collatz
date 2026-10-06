import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 070. -/
namespace Collatz.Research.RefinementAtlas.Batch070
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 22). -/
theorem data_8_22 : oddCount 22 8 = 4 ∧
    acceleratedOrbit 8 22 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_22 : gap 8 22 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_22 : threshold 8 22 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_22 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 22) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 22
  rw [data_8_22.1, data_8_22.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_22 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 22) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 22
  rw [data_8_22.1, data_8_22.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_22 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 22) < 256 * (2 * m) + 22 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 22 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_22] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 22) < 256 * (2 * m) + 22 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_22 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 22) < 256 * (2 * m + 1) + 22 := by
  apply refinement_cleared (k := 8) (r := 22) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_22]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 23). -/
theorem data_8_23 : oddCount 23 8 = 4 ∧
    acceleratedOrbit 8 23 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_23 : gap 8 23 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_23 : threshold 8 23 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_23 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 23) = 81 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 23
  rw [data_8_23.1, data_8_23.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_23 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 23) = 81 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 23
  rw [data_8_23.1, data_8_23.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_23 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 23) < 256 * (2 * m) + 23 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 23 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_23] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 23) < 256 * (2 * m) + 23 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_23 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 23) < 256 * (2 * m + 1) + 23 := by
  apply refinement_cleared (k := 8) (r := 23) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_23]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 24). -/
theorem data_8_24 : oddCount 24 8 = 2 ∧
    acceleratedOrbit 8 24 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_24 : gap 8 24 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_24 : threshold 8 24 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_24 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 24) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 24
  rw [data_8_24.1, data_8_24.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_24 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 24) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 24
  rw [data_8_24.1, data_8_24.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_24 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 24) < 256 * (2 * m) + 24 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 24 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_24] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 24) < 256 * (2 * m) + 24 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_24 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 24) < 256 * (2 * m + 1) + 24 := by
  apply refinement_cleared (k := 8) (r := 24) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_24]; decide

end Collatz.Research.RefinementAtlas.Batch070
