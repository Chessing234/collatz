import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 079. -/
namespace Collatz.Research.RefinementAtlas.Batch079
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 56). -/
theorem data_8_56 : oddCount 56 8 = 4 ∧
    acceleratedOrbit 8 56 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_56 : gap 8 56 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_56 : threshold 8 56 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_56 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 56) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 56
  rw [data_8_56.1, data_8_56.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_56 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 56) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 56
  rw [data_8_56.1, data_8_56.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_56 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 56) < 256 * (2 * m) + 56 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 56 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_56] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 56) < 256 * (2 * m) + 56 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_56 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 56) < 256 * (2 * m + 1) + 56 := by
  apply refinement_cleared (k := 8) (r := 56) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_56]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 57). -/
theorem data_8_57 : oddCount 57 8 = 5 ∧
    acceleratedOrbit 8 57 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_57 : gap 8 57 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_57 : threshold 8 57 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_57 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 57) = 243 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 57
  rw [data_8_57.1, data_8_57.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_57 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 57) = 243 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 57
  rw [data_8_57.1, data_8_57.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_57 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 57) < 256 * (2 * m) + 57 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 57 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_57] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 57) < 256 * (2 * m) + 57 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_57 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 57) < 256 * (2 * m + 1) + 57 := by
  apply refinement_cleared (k := 8) (r := 57) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_57]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 58). -/
theorem data_8_58 : oddCount 58 8 = 4 ∧
    acceleratedOrbit 8 58 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_58 : gap 8 58 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_58 : threshold 8 58 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_58 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 58) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 58
  rw [data_8_58.1, data_8_58.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_58 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 58) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 58
  rw [data_8_58.1, data_8_58.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_58 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 58) < 256 * (2 * m) + 58 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 58 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_58] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 58) < 256 * (2 * m) + 58 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_58 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 58) < 256 * (2 * m + 1) + 58 := by
  apply refinement_cleared (k := 8) (r := 58) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_58]; decide

end Collatz.Research.RefinementAtlas.Batch079
