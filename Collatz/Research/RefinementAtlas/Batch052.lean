import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 052. -/
namespace Collatz.Research.RefinementAtlas.Batch052
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 70). -/
theorem data_7_70 : oddCount 70 7 = 2 ∧
    acceleratedOrbit 7 70 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_70 : gap 7 70 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_70 : threshold 7 70 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_70 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 70) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 70
  rw [data_7_70.1, data_7_70.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_70 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 70) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 70
  rw [data_7_70.1, data_7_70.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_70 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 70) < 128 * (2 * m) + 70 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 70 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_70] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 70) < 128 * (2 * m) + 70 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_70 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 70) < 128 * (2 * m + 1) + 70 := by
  apply refinement_cleared (k := 7) (r := 70) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_70]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 72). -/
theorem data_7_72 : oddCount 72 7 = 3 ∧
    acceleratedOrbit 7 72 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_72 : gap 7 72 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_72 : threshold 7 72 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_72 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 72) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 72
  rw [data_7_72.1, data_7_72.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_72 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 72) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 72
  rw [data_7_72.1, data_7_72.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_72 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 72) < 128 * (2 * m) + 72 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 72 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_72] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 72) < 128 * (2 * m) + 72 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_72 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 72) < 128 * (2 * m + 1) + 72 := by
  apply refinement_cleared (k := 7) (r := 72) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_72]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 73). -/
theorem data_7_73 : oddCount 73 7 = 4 ∧
    acceleratedOrbit 7 73 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_73 : gap 7 73 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_73 : threshold 7 73 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_73 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 73) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 73
  rw [data_7_73.1, data_7_73.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_73 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 73) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 73
  rw [data_7_73.1, data_7_73.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_73 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 73) < 128 * (2 * m) + 73 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 73 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_73] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 73) < 128 * (2 * m) + 73 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_73 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 73) < 128 * (2 * m + 1) + 73 := by
  apply refinement_cleared (k := 7) (r := 73) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_73]; decide

end Collatz.Research.RefinementAtlas.Batch052
