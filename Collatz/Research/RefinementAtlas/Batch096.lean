import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 096. -/
namespace Collatz.Research.RefinementAtlas.Batch096
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 115). -/
theorem data_8_115 : oddCount 115 8 = 4 ∧
    acceleratedOrbit 8 115 = 37 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_115 : gap 8 115 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_115 : threshold 8 115 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_115 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 115) = 81 * (2 * m) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 115
  rw [data_8_115.1, data_8_115.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_115 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 115) = 81 * (2 * m + 1) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 115
  rw [data_8_115.1, data_8_115.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_115 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 115) < 256 * (2 * m) + 115 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 115 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_115] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 115) < 256 * (2 * m) + 115 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_115 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 115) < 256 * (2 * m + 1) + 115 := by
  apply refinement_cleared (k := 8) (r := 115) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_115]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 116). -/
theorem data_8_116 : oddCount 116 8 = 3 ∧
    acceleratedOrbit 8 116 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_116 : gap 8 116 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_116 : threshold 8 116 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_116 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 116) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 116
  rw [data_8_116.1, data_8_116.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_116 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 116) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 116
  rw [data_8_116.1, data_8_116.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_116 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 116) < 256 * (2 * m) + 116 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 116 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_116] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 116) < 256 * (2 * m) + 116 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_116 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 116) < 256 * (2 * m + 1) + 116 := by
  apply refinement_cleared (k := 8) (r := 116) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_116]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 117). -/
theorem data_8_117 : oddCount 117 8 = 3 ∧
    acceleratedOrbit 8 117 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_117 : gap 8 117 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_117 : threshold 8 117 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_117 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 117) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 117
  rw [data_8_117.1, data_8_117.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_117 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 117) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 117
  rw [data_8_117.1, data_8_117.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_117 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 117) < 256 * (2 * m) + 117 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 117 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_117] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 117) < 256 * (2 * m) + 117 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_117 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 117) < 256 * (2 * m + 1) + 117 := by
  apply refinement_cleared (k := 8) (r := 117) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_117]; decide

end Collatz.Research.RefinementAtlas.Batch096
