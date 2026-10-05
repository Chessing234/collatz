import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 191. -/
namespace Collatz.Research.RefinementAtlas.Batch191
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 215). -/
theorem data_9_215 : oddCount 215 9 = 5 ∧
    acceleratedOrbit 9 215 = 103 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_215 : gap 9 215 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_215 : threshold 9 215 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_215 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 215) = 243 * (2 * m) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 215
  rw [data_9_215.1, data_9_215.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_215 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 215) = 243 * (2 * m + 1) + 103 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 215
  rw [data_9_215.1, data_9_215.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_215 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 215) < 512 * (2 * m) + 215 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 215 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_215] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 215) < 512 * (2 * m) + 215 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_215 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 215) < 512 * (2 * m + 1) + 215 := by
  apply refinement_cleared (k := 9) (r := 215) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_215]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 216). -/
theorem data_9_216 : oddCount 216 9 = 5 ∧
    acceleratedOrbit 9 216 = 107 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_216 : gap 9 216 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_216 : threshold 9 216 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_216 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 216) = 243 * (2 * m) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 216
  rw [data_9_216.1, data_9_216.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_216 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 216) = 243 * (2 * m + 1) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 216
  rw [data_9_216.1, data_9_216.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_216 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 216) < 512 * (2 * m) + 216 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 216 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_216] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 216) < 512 * (2 * m) + 216 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_216 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 216) < 512 * (2 * m + 1) + 216 := by
  apply refinement_cleared (k := 9) (r := 216) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_216]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 217). -/
theorem data_9_217 : oddCount 217 9 = 4 ∧
    acceleratedOrbit 9 217 = 35 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_217 : gap 9 217 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_217 : threshold 9 217 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_217 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 217) = 81 * (2 * m) + 35 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 217
  rw [data_9_217.1, data_9_217.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_217 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 217) = 81 * (2 * m + 1) + 35 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 217
  rw [data_9_217.1, data_9_217.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_217 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 217) < 512 * (2 * m) + 217 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 217 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_217] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 217) < 512 * (2 * m) + 217 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_217 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 217) < 512 * (2 * m + 1) + 217 := by
  apply refinement_cleared (k := 9) (r := 217) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_217]; decide

end Collatz.Research.RefinementAtlas.Batch191
