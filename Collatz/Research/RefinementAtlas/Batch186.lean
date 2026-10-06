import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 186. -/
namespace Collatz.Research.RefinementAtlas.Batch186
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 198). -/
theorem data_9_198 : oddCount 198 9 = 3 ∧
    acceleratedOrbit 9 198 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_198 : gap 9 198 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_198 : threshold 9 198 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_198 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 198) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 198
  rw [data_9_198.1, data_9_198.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_198 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 198) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 198
  rw [data_9_198.1, data_9_198.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_198 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 198) < 512 * (2 * m) + 198 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 198 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_198] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 198) < 512 * (2 * m) + 198 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_198 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 198) < 512 * (2 * m + 1) + 198 := by
  apply refinement_cleared (k := 9) (r := 198) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_198]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 199). -/
theorem data_9_199 : oddCount 199 9 = 5 ∧
    acceleratedOrbit 9 199 = 95 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_199 : gap 9 199 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_199 : threshold 9 199 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_199 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 199) = 243 * (2 * m) + 95 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 199
  rw [data_9_199.1, data_9_199.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_199 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 199) = 243 * (2 * m + 1) + 95 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 199
  rw [data_9_199.1, data_9_199.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_199 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 199) < 512 * (2 * m) + 199 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 199 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_199] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 199) < 512 * (2 * m) + 199 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_199 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 199) < 512 * (2 * m + 1) + 199 := by
  apply refinement_cleared (k := 9) (r := 199) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_199]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 200). -/
theorem data_9_200 : oddCount 200 9 = 3 ∧
    acceleratedOrbit 9 200 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_200 : gap 9 200 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_200 : threshold 9 200 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_200 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 200) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 200
  rw [data_9_200.1, data_9_200.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_200 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 200) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 200
  rw [data_9_200.1, data_9_200.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_200 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 200) < 512 * (2 * m) + 200 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 200 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_200] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 200) < 512 * (2 * m) + 200 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_200 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 200) < 512 * (2 * m + 1) + 200 := by
  apply refinement_cleared (k := 9) (r := 200) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_200]; decide

end Collatz.Research.RefinementAtlas.Batch186
