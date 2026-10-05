import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 064. -/
namespace Collatz.Research.RefinementAtlas.Batch064
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 119). -/
theorem data_7_119 : oddCount 119 7 = 4 ∧
    acceleratedOrbit 7 119 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_119 : gap 7 119 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_119 : threshold 7 119 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_119 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 119) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 119
  rw [data_7_119.1, data_7_119.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_119 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 119) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 119
  rw [data_7_119.1, data_7_119.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_119 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 119) < 128 * (2 * m) + 119 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 119 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_119] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 119) < 128 * (2 * m) + 119 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_119 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 119) < 128 * (2 * m + 1) + 119 := by
  apply refinement_cleared (k := 7) (r := 119) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_119]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 120). -/
theorem data_7_120 : oddCount 120 7 = 4 ∧
    acceleratedOrbit 7 120 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_120 : gap 7 120 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_120 : threshold 7 120 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_120 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 120) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 120
  rw [data_7_120.1, data_7_120.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_120 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 120) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 120
  rw [data_7_120.1, data_7_120.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_120 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 120) < 128 * (2 * m) + 120 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 120 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_120] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 120) < 128 * (2 * m) + 120 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_120 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 120) < 128 * (2 * m + 1) + 120 := by
  apply refinement_cleared (k := 7) (r := 120) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_120]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 122). -/
theorem data_7_122 : oddCount 122 7 = 4 ∧
    acceleratedOrbit 7 122 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_122 : gap 7 122 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_122 : threshold 7 122 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_122 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 122) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 122
  rw [data_7_122.1, data_7_122.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_122 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 122) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 122
  rw [data_7_122.1, data_7_122.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_122 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 122) < 128 * (2 * m) + 122 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 122 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_122] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 122) < 128 * (2 * m) + 122 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_122 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 122) < 128 * (2 * m + 1) + 122 := by
  apply refinement_cleared (k := 7) (r := 122) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_122]; decide

end Collatz.Research.RefinementAtlas.Batch064
