import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 194. -/
namespace Collatz.Research.RefinementAtlas.Batch194
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 228). -/
theorem data_9_228 : oddCount 228 9 = 4 ∧
    acceleratedOrbit 9 228 = 37 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_228 : gap 9 228 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_228 : threshold 9 228 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_228 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 228) = 81 * (2 * m) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 228
  rw [data_9_228.1, data_9_228.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_228 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 228) = 81 * (2 * m + 1) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 228
  rw [data_9_228.1, data_9_228.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_228 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 228) < 512 * (2 * m) + 228 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 228 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_228] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 228) < 512 * (2 * m) + 228 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_228 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 228) < 512 * (2 * m + 1) + 228 := by
  apply refinement_cleared (k := 9) (r := 228) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_228]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 229). -/
theorem data_9_229 : oddCount 229 9 = 4 ∧
    acceleratedOrbit 9 229 = 37 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_229 : gap 9 229 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_229 : threshold 9 229 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_229 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 229) = 81 * (2 * m) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 229
  rw [data_9_229.1, data_9_229.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_229 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 229) = 81 * (2 * m + 1) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 229
  rw [data_9_229.1, data_9_229.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_229 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 229) < 512 * (2 * m) + 229 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 229 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_229] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 229) < 512 * (2 * m) + 229 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_229 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 229) < 512 * (2 * m + 1) + 229 := by
  apply refinement_cleared (k := 9) (r := 229) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_229]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 230). -/
theorem data_9_230 : oddCount 230 9 = 4 ∧
    acceleratedOrbit 9 230 = 37 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_230 : gap 9 230 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_230 : threshold 9 230 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_230 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 230) = 81 * (2 * m) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 230
  rw [data_9_230.1, data_9_230.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_230 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 230) = 81 * (2 * m + 1) + 37 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 230
  rw [data_9_230.1, data_9_230.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_230 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 230) < 512 * (2 * m) + 230 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 230 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_230] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 230) < 512 * (2 * m) + 230 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_230 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 230) < 512 * (2 * m + 1) + 230 := by
  apply refinement_cleared (k := 9) (r := 230) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_230]; decide

end Collatz.Research.RefinementAtlas.Batch194
