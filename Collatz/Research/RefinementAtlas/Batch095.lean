import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 095. -/
namespace Collatz.Research.RefinementAtlas.Batch095
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 112). -/
theorem data_8_112 : oddCount 112 8 = 3 ∧
    acceleratedOrbit 8 112 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_112 : gap 8 112 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_112 : threshold 8 112 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_112 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 112) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 112
  rw [data_8_112.1, data_8_112.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_112 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 112) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 112
  rw [data_8_112.1, data_8_112.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_112 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 112) < 256 * (2 * m) + 112 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 112 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_112] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 112) < 256 * (2 * m) + 112 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_112 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 112) < 256 * (2 * m + 1) + 112 := by
  apply refinement_cleared (k := 8) (r := 112) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_112]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 113). -/
theorem data_8_113 : oddCount 113 8 = 2 ∧
    acceleratedOrbit 8 113 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_113 : gap 8 113 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_113 : threshold 8 113 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_113 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 113) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 113
  rw [data_8_113.1, data_8_113.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_113 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 113) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 113
  rw [data_8_113.1, data_8_113.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_113 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 113) < 256 * (2 * m) + 113 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 113 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_113] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 113) < 256 * (2 * m) + 113 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_113 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 113) < 256 * (2 * m + 1) + 113 := by
  apply refinement_cleared (k := 8) (r := 113) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_113]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 114). -/
theorem data_8_114 : oddCount 114 8 = 4 ∧
    acceleratedOrbit 8 114 = 37 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_114 : gap 8 114 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_114 : threshold 8 114 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_114 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 114) = 81 * (2 * m) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 114
  rw [data_8_114.1, data_8_114.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_114 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 114) = 81 * (2 * m + 1) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 114
  rw [data_8_114.1, data_8_114.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_114 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 114) < 256 * (2 * m) + 114 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 114 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_114] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 114) < 256 * (2 * m) + 114 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_114 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 114) < 256 * (2 * m + 1) + 114 := by
  apply refinement_cleared (k := 8) (r := 114) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_114]; decide

end Collatz.Research.RefinementAtlas.Batch095
