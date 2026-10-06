import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 090. -/
namespace Collatz.Research.RefinementAtlas.Batch090
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 95). -/
theorem data_8_95 : oddCount 95 8 = 5 ∧
    acceleratedOrbit 8 95 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_95 : gap 8 95 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_95 : threshold 8 95 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_95 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 95) = 243 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 95
  rw [data_8_95.1, data_8_95.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_95 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 95) = 243 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 95
  rw [data_8_95.1, data_8_95.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_95 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 95) < 256 * (2 * m) + 95 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 95 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_95] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 95) < 256 * (2 * m) + 95 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_95 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 95) < 256 * (2 * m + 1) + 95 := by
  apply refinement_cleared (k := 8) (r := 95) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_95]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 96). -/
theorem data_8_96 : oddCount 96 8 = 2 ∧
    acceleratedOrbit 8 96 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_96 : gap 8 96 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_96 : threshold 8 96 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_96 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 96) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 96
  rw [data_8_96.1, data_8_96.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_96 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 96) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 96
  rw [data_8_96.1, data_8_96.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_96 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 96) < 256 * (2 * m) + 96 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 96 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_96] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 96) < 256 * (2 * m) + 96 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_96 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 96) < 256 * (2 * m + 1) + 96 := by
  apply refinement_cleared (k := 8) (r := 96) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_96]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 97). -/
theorem data_8_97 : oddCount 97 8 = 5 ∧
    acceleratedOrbit 8 97 = 94 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_97 : gap 8 97 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_97 : threshold 8 97 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_97 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 97) = 243 * (2 * m) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 97
  rw [data_8_97.1, data_8_97.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_97 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 97) = 243 * (2 * m + 1) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 97
  rw [data_8_97.1, data_8_97.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_97 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 97) < 256 * (2 * m) + 97 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 97 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_97] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 97) < 256 * (2 * m) + 97 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_97 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 97) < 256 * (2 * m + 1) + 97 := by
  apply refinement_cleared (k := 8) (r := 97) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_97]; decide

end Collatz.Research.RefinementAtlas.Batch090
