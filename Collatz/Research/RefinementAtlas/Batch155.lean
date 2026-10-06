import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 155. -/
namespace Collatz.Research.RefinementAtlas.Batch155
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 69). -/
theorem data_9_69 : oddCount 69 9 = 3 ∧
    acceleratedOrbit 9 69 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_69 : gap 9 69 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_69 : threshold 9 69 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_69 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 69) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 69
  rw [data_9_69.1, data_9_69.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_69 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 69) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 69
  rw [data_9_69.1, data_9_69.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_69 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 69) < 512 * (2 * m) + 69 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 69 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_69] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 69) < 512 * (2 * m) + 69 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_69 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 69) < 512 * (2 * m + 1) + 69 := by
  apply refinement_cleared (k := 9) (r := 69) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_69]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 70). -/
theorem data_9_70 : oddCount 70 9 = 3 ∧
    acceleratedOrbit 9 70 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_70 : gap 9 70 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_70 : threshold 9 70 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_70 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 70) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 70
  rw [data_9_70.1, data_9_70.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_70 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 70) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 70
  rw [data_9_70.1, data_9_70.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_70 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 70) < 512 * (2 * m) + 70 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 70 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_70] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 70) < 512 * (2 * m) + 70 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_70 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 70) < 512 * (2 * m + 1) + 70 := by
  apply refinement_cleared (k := 9) (r := 70) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_70]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 72). -/
theorem data_9_72 : oddCount 72 9 = 4 ∧
    acceleratedOrbit 9 72 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_72 : gap 9 72 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_72 : threshold 9 72 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_72 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 72) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 72
  rw [data_9_72.1, data_9_72.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_72 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 72) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 72
  rw [data_9_72.1, data_9_72.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_72 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 72) < 512 * (2 * m) + 72 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 72 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_72] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 72) < 512 * (2 * m) + 72 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_72 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 72) < 512 * (2 * m + 1) + 72 := by
  apply refinement_cleared (k := 9) (r := 72) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_72]; decide

end Collatz.Research.RefinementAtlas.Batch155
