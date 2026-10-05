import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 053. -/
namespace Collatz.Research.RefinementAtlas.Batch053
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 74). -/
theorem data_7_74 : oddCount 74 7 = 3 ∧
    acceleratedOrbit 7 74 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_74 : gap 7 74 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_74 : threshold 7 74 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_74 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 74) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 74
  rw [data_7_74.1, data_7_74.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_74 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 74) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 74
  rw [data_7_74.1, data_7_74.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_74 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 74) < 128 * (2 * m) + 74 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 74 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_74] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 74) < 128 * (2 * m) + 74 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_74 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 74) < 128 * (2 * m + 1) + 74 := by
  apply refinement_cleared (k := 7) (r := 74) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_74]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 75). -/
theorem data_7_75 : oddCount 75 7 = 3 ∧
    acceleratedOrbit 7 75 = 16 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_75 : gap 7 75 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_75 : threshold 7 75 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_75 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 75) = 27 * (2 * m) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 75
  rw [data_7_75.1, data_7_75.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_75 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 75) = 27 * (2 * m + 1) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 75
  rw [data_7_75.1, data_7_75.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_75 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 75) < 128 * (2 * m) + 75 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 75 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_75] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 75) < 128 * (2 * m) + 75 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_75 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 75) < 128 * (2 * m + 1) + 75 := by
  apply refinement_cleared (k := 7) (r := 75) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_75]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 76). -/
theorem data_7_76 : oddCount 76 7 = 3 ∧
    acceleratedOrbit 7 76 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_76 : gap 7 76 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_76 : threshold 7 76 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_76 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 76) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 76
  rw [data_7_76.1, data_7_76.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_76 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 76) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 76
  rw [data_7_76.1, data_7_76.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_76 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 76) < 128 * (2 * m) + 76 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 76 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_76] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 76) < 128 * (2 * m) + 76 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_76 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 76) < 128 * (2 * m + 1) + 76 := by
  apply refinement_cleared (k := 7) (r := 76) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_76]; decide

end Collatz.Research.RefinementAtlas.Batch053
