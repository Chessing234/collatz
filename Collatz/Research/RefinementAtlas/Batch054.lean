import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 054. -/
namespace Collatz.Research.RefinementAtlas.Batch054
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 77). -/
theorem data_7_77 : oddCount 77 7 = 3 ∧
    acceleratedOrbit 7 77 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_77 : gap 7 77 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_77 : threshold 7 77 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_77 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 77) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 77
  rw [data_7_77.1, data_7_77.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_77 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 77) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 77
  rw [data_7_77.1, data_7_77.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_77 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 77) < 128 * (2 * m) + 77 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 77 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_77] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 77) < 128 * (2 * m) + 77 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_77 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 77) < 128 * (2 * m + 1) + 77 := by
  apply refinement_cleared (k := 7) (r := 77) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_77]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 80). -/
theorem data_7_80 : oddCount 80 7 = 1 ∧
    acceleratedOrbit 7 80 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_80 : gap 7 80 = 125 ∧ 3 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_80 : threshold 7 80 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_80 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 80) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 80
  rw [data_7_80.1, data_7_80.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_80 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 80) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 80
  rw [data_7_80.1, data_7_80.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_80 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 80) < 128 * (2 * m) + 80 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 80 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_80] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 80) < 128 * (2 * m) + 80 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_80 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 80) < 128 * (2 * m + 1) + 80 := by
  apply refinement_cleared (k := 7) (r := 80) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_80]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 81). -/
theorem data_7_81 : oddCount 81 7 = 4 ∧
    acceleratedOrbit 7 81 = 53 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_81 : gap 7 81 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_81 : threshold 7 81 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_81 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 81) = 81 * (2 * m) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 81
  rw [data_7_81.1, data_7_81.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_81 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 81) = 81 * (2 * m + 1) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 81
  rw [data_7_81.1, data_7_81.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_81 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 81) < 128 * (2 * m) + 81 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 81 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_81] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 81) < 128 * (2 * m) + 81 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_81 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 81) < 128 * (2 * m + 1) + 81 := by
  apply refinement_cleared (k := 7) (r := 81) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_81]; decide

end Collatz.Research.RefinementAtlas.Batch054
