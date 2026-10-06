import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 200. -/
namespace Collatz.Research.RefinementAtlas.Batch200
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 257). -/
theorem data_9_257 : oddCount 257 9 = 4 ∧
    acceleratedOrbit 9 257 = 41 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_257 : gap 9 257 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_257 : threshold 9 257 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_257 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 257) = 81 * (2 * m) + 41 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 257
  rw [data_9_257.1, data_9_257.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_257 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 257) = 81 * (2 * m + 1) + 41 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 257
  rw [data_9_257.1, data_9_257.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_257 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 257) < 512 * (2 * m) + 257 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 257 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_257] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 257) < 512 * (2 * m) + 257 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_257 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 257) < 512 * (2 * m + 1) + 257 := by
  apply refinement_cleared (k := 9) (r := 257) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_257]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 258). -/
theorem data_9_258 : oddCount 258 9 = 5 ∧
    acceleratedOrbit 9 258 = 125 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_258 : gap 9 258 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_258 : threshold 9 258 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_258 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 258) = 243 * (2 * m) + 125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 258
  rw [data_9_258.1, data_9_258.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_258 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 258) = 243 * (2 * m + 1) + 125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 258
  rw [data_9_258.1, data_9_258.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_258 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 258) < 512 * (2 * m) + 258 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 258 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_258] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 258) < 512 * (2 * m) + 258 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_258 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 258) < 512 * (2 * m + 1) + 258 := by
  apply refinement_cleared (k := 9) (r := 258) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_258]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 259). -/
theorem data_9_259 : oddCount 259 9 = 5 ∧
    acceleratedOrbit 9 259 = 125 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_259 : gap 9 259 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_259 : threshold 9 259 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_259 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 259) = 243 * (2 * m) + 125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 259
  rw [data_9_259.1, data_9_259.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_259 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 259) = 243 * (2 * m + 1) + 125 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 259
  rw [data_9_259.1, data_9_259.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_259 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 259) < 512 * (2 * m) + 259 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 259 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_259] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 259) < 512 * (2 * m) + 259 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_259 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 259) < 512 * (2 * m + 1) + 259 := by
  apply refinement_cleared (k := 9) (r := 259) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_259]; decide

end Collatz.Research.RefinementAtlas.Batch200
