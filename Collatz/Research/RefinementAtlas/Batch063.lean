import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 063. -/
namespace Collatz.Research.RefinementAtlas.Batch063
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 116). -/
theorem data_7_116 : oddCount 116 7 = 3 ∧
    acceleratedOrbit 7 116 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_116 : gap 7 116 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_116 : threshold 7 116 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_116 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 116) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 116
  rw [data_7_116.1, data_7_116.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_116 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 116) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 116
  rw [data_7_116.1, data_7_116.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_116 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 116) < 128 * (2 * m) + 116 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 116 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_116] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 116) < 128 * (2 * m) + 116 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_116 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 116) < 128 * (2 * m + 1) + 116 := by
  apply refinement_cleared (k := 7) (r := 116) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_116]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 117). -/
theorem data_7_117 : oddCount 117 7 = 3 ∧
    acceleratedOrbit 7 117 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_117 : gap 7 117 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_117 : threshold 7 117 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_117 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 117) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 117
  rw [data_7_117.1, data_7_117.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_117 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 117) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 117
  rw [data_7_117.1, data_7_117.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_117 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 117) < 128 * (2 * m) + 117 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 117 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_117] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 117) < 128 * (2 * m) + 117 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_117 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 117) < 128 * (2 * m + 1) + 117 := by
  apply refinement_cleared (k := 7) (r := 117) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_117]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 118). -/
theorem data_7_118 : oddCount 118 7 = 4 ∧
    acceleratedOrbit 7 118 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_118 : gap 7 118 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_118 : threshold 7 118 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_118 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 118) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 118
  rw [data_7_118.1, data_7_118.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_118 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 118) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 118
  rw [data_7_118.1, data_7_118.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_118 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 118) < 128 * (2 * m) + 118 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 118 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_118] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 118) < 128 * (2 * m) + 118 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_118 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 118) < 128 * (2 * m + 1) + 118 := by
  apply refinement_cleared (k := 7) (r := 118) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_118]; decide

end Collatz.Research.RefinementAtlas.Batch063
