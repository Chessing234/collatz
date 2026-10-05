import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 137. -/
namespace Collatz.Research.RefinementAtlas.Batch137
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 7). -/
theorem data_9_7 : oddCount 7 9 = 5 ∧
    acceleratedOrbit 9 7 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_7 : gap 9 7 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_7 : threshold 9 7 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_7 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 7) = 243 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 7
  rw [data_9_7.1, data_9_7.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_7 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 7) = 243 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 7
  rw [data_9_7.1, data_9_7.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_7 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 7) < 512 * (2 * m) + 7 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 7 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_7] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 7) < 512 * (2 * m) + 7 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_7 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 7) < 512 * (2 * m + 1) + 7 := by
  apply refinement_cleared (k := 9) (r := 7) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_7]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 8). -/
theorem data_9_8 : oddCount 8 9 = 3 ∧
    acceleratedOrbit 9 8 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_8 : gap 9 8 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_8 : threshold 9 8 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_8 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 8) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 8
  rw [data_9_8.1, data_9_8.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_8 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 8) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 8
  rw [data_9_8.1, data_9_8.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_8 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 8) < 512 * (2 * m) + 8 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 8 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_8] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 8) < 512 * (2 * m) + 8 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_8 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 8) < 512 * (2 * m + 1) + 8 := by
  apply refinement_cleared (k := 9) (r := 8) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_8]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 9). -/
theorem data_9_9 : oddCount 9 9 = 5 ∧
    acceleratedOrbit 9 9 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_9 : gap 9 9 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_9 : threshold 9 9 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_9 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 9) = 243 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 9
  rw [data_9_9.1, data_9_9.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_9 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 9) = 243 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 9
  rw [data_9_9.1, data_9_9.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_9 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 9) < 512 * (2 * m) + 9 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 9 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_9] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 9) < 512 * (2 * m) + 9 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_9 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 9) < 512 * (2 * m + 1) + 9 := by
  apply refinement_cleared (k := 9) (r := 9) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_9]; decide

end Collatz.Research.RefinementAtlas.Batch137
