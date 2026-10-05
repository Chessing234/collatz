import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 040. -/
namespace Collatz.Research.RefinementAtlas.Batch040
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 25). -/
theorem data_7_25 : oddCount 25 7 = 4 ∧
    acceleratedOrbit 7 25 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_25 : gap 7 25 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_25 : threshold 7 25 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_25 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 25) = 81 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 25
  rw [data_7_25.1, data_7_25.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_25 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 25) = 81 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 25
  rw [data_7_25.1, data_7_25.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_25 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 25) < 128 * (2 * m) + 25 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 25 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_25] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 25) < 128 * (2 * m) + 25 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_25 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 25) < 128 * (2 * m + 1) + 25 := by
  apply refinement_cleared (k := 7) (r := 25) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_25]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 26). -/
theorem data_7_26 : oddCount 26 7 = 2 ∧
    acceleratedOrbit 7 26 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_26 : gap 7 26 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_26 : threshold 7 26 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_26 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 26) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 26
  rw [data_7_26.1, data_7_26.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_26 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 26) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 26
  rw [data_7_26.1, data_7_26.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_26 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 26) < 128 * (2 * m) + 26 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 26 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_26] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 26) < 128 * (2 * m) + 26 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_26 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 26) < 128 * (2 * m + 1) + 26 := by
  apply refinement_cleared (k := 7) (r := 26) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_26]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 28). -/
theorem data_7_28 : oddCount 28 7 = 4 ∧
    acceleratedOrbit 7 28 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_28 : gap 7 28 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_28 : threshold 7 28 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_28 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 28) = 81 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 28
  rw [data_7_28.1, data_7_28.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_28 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 28) = 81 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 28
  rw [data_7_28.1, data_7_28.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_28 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 28) < 128 * (2 * m) + 28 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 28 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_28] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 28) < 128 * (2 * m) + 28 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_28 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 28) < 128 * (2 * m + 1) + 28 := by
  apply refinement_cleared (k := 7) (r := 28) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_28]; decide

end Collatz.Research.RefinementAtlas.Batch040
