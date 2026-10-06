import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 156. -/
namespace Collatz.Research.RefinementAtlas.Batch156
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 74). -/
theorem data_9_74 : oddCount 74 9 = 4 ∧
    acceleratedOrbit 9 74 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_74 : gap 9 74 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_74 : threshold 9 74 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_74 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 74) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 74
  rw [data_9_74.1, data_9_74.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_74 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 74) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 74
  rw [data_9_74.1, data_9_74.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_74 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 74) < 512 * (2 * m) + 74 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 74 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_74] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 74) < 512 * (2 * m) + 74 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_74 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 74) < 512 * (2 * m + 1) + 74 := by
  apply refinement_cleared (k := 9) (r := 74) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_74]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 75). -/
theorem data_9_75 : oddCount 75 9 = 3 ∧
    acceleratedOrbit 9 75 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_75 : gap 9 75 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_75 : threshold 9 75 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_75 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 75) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 75
  rw [data_9_75.1, data_9_75.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_75 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 75) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 75
  rw [data_9_75.1, data_9_75.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_75 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 75) < 512 * (2 * m) + 75 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 75 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_75] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 75) < 512 * (2 * m) + 75 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_75 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 75) < 512 * (2 * m + 1) + 75 := by
  apply refinement_cleared (k := 9) (r := 75) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_75]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 76). -/
theorem data_9_76 : oddCount 76 9 = 4 ∧
    acceleratedOrbit 9 76 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_76 : gap 9 76 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_76 : threshold 9 76 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_76 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 76) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 76
  rw [data_9_76.1, data_9_76.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_76 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 76) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 76
  rw [data_9_76.1, data_9_76.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_76 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 76) < 512 * (2 * m) + 76 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 76 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_76] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 76) < 512 * (2 * m) + 76 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_76 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 76) < 512 * (2 * m + 1) + 76 := by
  apply refinement_cleared (k := 9) (r := 76) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_76]; decide

end Collatz.Research.RefinementAtlas.Batch156
