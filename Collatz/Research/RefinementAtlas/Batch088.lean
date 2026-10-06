import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 088. -/
namespace Collatz.Research.RefinementAtlas.Batch088
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 88). -/
theorem data_8_88 : oddCount 88 8 = 3 ∧
    acceleratedOrbit 8 88 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_88 : gap 8 88 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_88 : threshold 8 88 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_88 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 88) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 88
  rw [data_8_88.1, data_8_88.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_88 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 88) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 88
  rw [data_8_88.1, data_8_88.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_88 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 88) < 256 * (2 * m) + 88 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 88 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_88] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 88) < 256 * (2 * m) + 88 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_88 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 88) < 256 * (2 * m + 1) + 88 := by
  apply refinement_cleared (k := 8) (r := 88) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_88]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 89). -/
theorem data_8_89 : oddCount 89 8 = 4 ∧
    acceleratedOrbit 8 89 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_89 : gap 8 89 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_89 : threshold 8 89 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_89 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 89) = 81 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 89
  rw [data_8_89.1, data_8_89.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_89 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 89) = 81 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 89
  rw [data_8_89.1, data_8_89.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_89 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 89) < 256 * (2 * m) + 89 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 89 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_89] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 89) < 256 * (2 * m) + 89 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_89 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 89) < 256 * (2 * m + 1) + 89 := by
  apply refinement_cleared (k := 8) (r := 89) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_89]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 90). -/
theorem data_8_90 : oddCount 90 8 = 3 ∧
    acceleratedOrbit 8 90 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_90 : gap 8 90 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_90 : threshold 8 90 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_90 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 90) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 90
  rw [data_8_90.1, data_8_90.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_90 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 90) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 90
  rw [data_8_90.1, data_8_90.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_90 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 90) < 256 * (2 * m) + 90 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 90 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_90] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 90) < 256 * (2 * m) + 90 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_90 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 90) < 256 * (2 * m + 1) + 90 := by
  apply refinement_cleared (k := 8) (r := 90) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_90]; decide

end Collatz.Research.RefinementAtlas.Batch088
