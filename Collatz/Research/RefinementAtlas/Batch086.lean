import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 086. -/
namespace Collatz.Research.RefinementAtlas.Batch086
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 80). -/
theorem data_8_80 : oddCount 80 8 = 1 ∧
    acceleratedOrbit 8 80 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_80 : gap 8 80 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_80 : threshold 8 80 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_80 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 80) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 80
  rw [data_8_80.1, data_8_80.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_80 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 80) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 80
  rw [data_8_80.1, data_8_80.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_80 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 80) < 256 * (2 * m) + 80 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 80 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_80] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 80) < 256 * (2 * m) + 80 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_80 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 80) < 256 * (2 * m + 1) + 80 := by
  apply refinement_cleared (k := 8) (r := 80) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_80]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 81). -/
theorem data_8_81 : oddCount 81 8 = 5 ∧
    acceleratedOrbit 8 81 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_81 : gap 8 81 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_81 : threshold 8 81 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_81 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 81) = 243 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 81
  rw [data_8_81.1, data_8_81.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_81 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 81) = 243 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 81
  rw [data_8_81.1, data_8_81.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_81 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 81) < 256 * (2 * m) + 81 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 81 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_81] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 81) < 256 * (2 * m) + 81 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_81 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 81) < 256 * (2 * m + 1) + 81 := by
  apply refinement_cleared (k := 8) (r := 81) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_81]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 84). -/
theorem data_8_84 : oddCount 84 8 = 1 ∧
    acceleratedOrbit 8 84 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_84 : gap 8 84 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_84 : threshold 8 84 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_84 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 84) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 84
  rw [data_8_84.1, data_8_84.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_84 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 84) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 84
  rw [data_8_84.1, data_8_84.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_84 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 84) < 256 * (2 * m) + 84 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 84 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_84] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 84) < 256 * (2 * m) + 84 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_84 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 84) < 256 * (2 * m + 1) + 84 := by
  apply refinement_cleared (k := 8) (r := 84) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_84]; decide

end Collatz.Research.RefinementAtlas.Batch086
