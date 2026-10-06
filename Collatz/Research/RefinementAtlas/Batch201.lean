import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 201. -/
namespace Collatz.Research.RefinementAtlas.Batch201
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 260). -/
theorem data_9_260 : oddCount 260 9 = 3 ∧
    acceleratedOrbit 9 260 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_260 : gap 9 260 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_260 : threshold 9 260 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_260 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 260) = 27 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 260
  rw [data_9_260.1, data_9_260.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_260 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 260) = 27 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 260
  rw [data_9_260.1, data_9_260.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_260 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 260) < 512 * (2 * m) + 260 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 260 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_260] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 260) < 512 * (2 * m) + 260 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_260 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 260) < 512 * (2 * m + 1) + 260 := by
  apply refinement_cleared (k := 9) (r := 260) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_260]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 261). -/
theorem data_9_261 : oddCount 261 9 = 3 ∧
    acceleratedOrbit 9 261 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_261 : gap 9 261 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_261 : threshold 9 261 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_261 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 261) = 27 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 261
  rw [data_9_261.1, data_9_261.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_261 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 261) = 27 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 261
  rw [data_9_261.1, data_9_261.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_261 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 261) < 512 * (2 * m) + 261 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 261 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_261] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 261) < 512 * (2 * m) + 261 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_261 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 261) < 512 * (2 * m + 1) + 261 := by
  apply refinement_cleared (k := 9) (r := 261) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_261]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 262). -/
theorem data_9_262 : oddCount 262 9 = 3 ∧
    acceleratedOrbit 9 262 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_262 : gap 9 262 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_262 : threshold 9 262 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_262 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 262) = 27 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 262
  rw [data_9_262.1, data_9_262.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_262 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 262) = 27 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 262
  rw [data_9_262.1, data_9_262.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_262 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 262) < 512 * (2 * m) + 262 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 262 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_262] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 262) < 512 * (2 * m) + 262 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_262 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 262) < 512 * (2 * m + 1) + 262 := by
  apply refinement_cleared (k := 9) (r := 262) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_262]; decide

end Collatz.Research.RefinementAtlas.Batch201
