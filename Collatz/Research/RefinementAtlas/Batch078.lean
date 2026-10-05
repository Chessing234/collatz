import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 078. -/
namespace Collatz.Research.RefinementAtlas.Batch078
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 51). -/
theorem data_8_51 : oddCount 51 8 = 4 ∧
    acceleratedOrbit 8 51 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_51 : gap 8 51 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_51 : threshold 8 51 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_51 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 51) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 51
  rw [data_8_51.1, data_8_51.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_51 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 51) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 51
  rw [data_8_51.1, data_8_51.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_51 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 51) < 256 * (2 * m) + 51 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 51 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_51] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 51) < 256 * (2 * m) + 51 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_51 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 51) < 256 * (2 * m + 1) + 51 := by
  apply refinement_cleared (k := 8) (r := 51) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_51]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 52). -/
theorem data_8_52 : oddCount 52 8 = 2 ∧
    acceleratedOrbit 8 52 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_52 : gap 8 52 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_52 : threshold 8 52 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_52 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 52) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 52
  rw [data_8_52.1, data_8_52.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_52 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 52) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 52
  rw [data_8_52.1, data_8_52.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_52 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 52) < 256 * (2 * m) + 52 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 52 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_52] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 52) < 256 * (2 * m) + 52 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_52 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 52) < 256 * (2 * m + 1) + 52 := by
  apply refinement_cleared (k := 8) (r := 52) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_52]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 53). -/
theorem data_8_53 : oddCount 53 8 = 2 ∧
    acceleratedOrbit 8 53 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_53 : gap 8 53 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_53 : threshold 8 53 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_53 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 53) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 53
  rw [data_8_53.1, data_8_53.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_53 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 53) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 53
  rw [data_8_53.1, data_8_53.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_53 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 53) < 256 * (2 * m) + 53 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 53 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_53] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 53) < 256 * (2 * m) + 53 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_53 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 53) < 256 * (2 * m + 1) + 53 := by
  apply refinement_cleared (k := 8) (r := 53) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_53]; decide

end Collatz.Research.RefinementAtlas.Batch078
