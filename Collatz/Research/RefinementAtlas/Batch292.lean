import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 292. -/
namespace Collatz.Research.RefinementAtlas.Batch292
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 114). -/
theorem data_10_114 : oddCount 114 10 = 5 ∧
    acceleratedOrbit 10 114 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_114 : gap 10 114 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_114 : threshold 10 114 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_114 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 114) = 243 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 114
  rw [data_10_114.1, data_10_114.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_114 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 114) = 243 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 114
  rw [data_10_114.1, data_10_114.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_114 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 114) < 1024 * (2 * m) + 114 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 114 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_114] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 114) < 1024 * (2 * m) + 114 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_114 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 114) < 1024 * (2 * m + 1) + 114 := by
  apply refinement_cleared (k := 10) (r := 114) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_114]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 115). -/
theorem data_10_115 : oddCount 115 10 = 5 ∧
    acceleratedOrbit 10 115 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_115 : gap 10 115 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_115 : threshold 10 115 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_115 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 115) = 243 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 115
  rw [data_10_115.1, data_10_115.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_115 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 115) = 243 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 115
  rw [data_10_115.1, data_10_115.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_115 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 115) < 1024 * (2 * m) + 115 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 115 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_115] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 115) < 1024 * (2 * m) + 115 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_115 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 115) < 1024 * (2 * m + 1) + 115 := by
  apply refinement_cleared (k := 10) (r := 115) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_115]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 116). -/
theorem data_10_116 : oddCount 116 10 = 4 ∧
    acceleratedOrbit 10 116 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_116 : gap 10 116 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_116 : threshold 10 116 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_116 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 116) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 116
  rw [data_10_116.1, data_10_116.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_116 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 116) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 116
  rw [data_10_116.1, data_10_116.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_116 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 116) < 1024 * (2 * m) + 116 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 116 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_116] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 116) < 1024 * (2 * m) + 116 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_116 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 116) < 1024 * (2 * m + 1) + 116 := by
  apply refinement_cleared (k := 10) (r := 116) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_116]; decide

end Collatz.Research.RefinementAtlas.Batch292
