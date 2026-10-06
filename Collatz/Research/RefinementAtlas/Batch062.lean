import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 062. -/
namespace Collatz.Research.RefinementAtlas.Batch062
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 113). -/
theorem data_7_113 : oddCount 113 7 = 2 ∧
    acceleratedOrbit 7 113 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_113 : gap 7 113 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_113 : threshold 7 113 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_113 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 113) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 113
  rw [data_7_113.1, data_7_113.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_113 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 113) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 113
  rw [data_7_113.1, data_7_113.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_113 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 113) < 128 * (2 * m) + 113 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 113 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_113] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 113) < 128 * (2 * m) + 113 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_113 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 113) < 128 * (2 * m + 1) + 113 := by
  apply refinement_cleared (k := 7) (r := 113) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_113]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 114). -/
theorem data_7_114 : oddCount 114 7 = 4 ∧
    acceleratedOrbit 7 114 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_114 : gap 7 114 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_114 : threshold 7 114 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_114 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 114) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 114
  rw [data_7_114.1, data_7_114.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_114 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 114) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 114
  rw [data_7_114.1, data_7_114.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_114 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 114) < 128 * (2 * m) + 114 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 114 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_114] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 114) < 128 * (2 * m) + 114 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_114 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 114) < 128 * (2 * m + 1) + 114 := by
  apply refinement_cleared (k := 7) (r := 114) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_114]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 115). -/
theorem data_7_115 : oddCount 115 7 = 4 ∧
    acceleratedOrbit 7 115 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_115 : gap 7 115 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_115 : threshold 7 115 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_115 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 115) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 115
  rw [data_7_115.1, data_7_115.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_115 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 115) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 115
  rw [data_7_115.1, data_7_115.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_115 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 115) < 128 * (2 * m) + 115 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 115 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_115] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 115) < 128 * (2 * m) + 115 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_115 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 115) < 128 * (2 * m + 1) + 115 := by
  apply refinement_cleared (k := 7) (r := 115) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_115]; decide

end Collatz.Research.RefinementAtlas.Batch062
