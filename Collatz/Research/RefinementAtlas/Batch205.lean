import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 205. -/
namespace Collatz.Research.RefinementAtlas.Batch205
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 276). -/
theorem data_9_276 : oddCount 276 9 = 2 ∧
    acceleratedOrbit 9 276 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_276 : gap 9 276 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_276 : threshold 9 276 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_276 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 276) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 276
  rw [data_9_276.1, data_9_276.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_276 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 276) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 276
  rw [data_9_276.1, data_9_276.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_276 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 276) < 512 * (2 * m) + 276 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 276 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_276] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 276) < 512 * (2 * m) + 276 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_276 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 276) < 512 * (2 * m + 1) + 276 := by
  apply refinement_cleared (k := 9) (r := 276) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_276]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 277). -/
theorem data_9_277 : oddCount 277 9 = 2 ∧
    acceleratedOrbit 9 277 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_277 : gap 9 277 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_277 : threshold 9 277 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_277 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 277) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 277
  rw [data_9_277.1, data_9_277.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_277 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 277) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 277
  rw [data_9_277.1, data_9_277.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_277 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 277) < 512 * (2 * m) + 277 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 277 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_277] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 277) < 512 * (2 * m) + 277 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_277 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 277) < 512 * (2 * m + 1) + 277 := by
  apply refinement_cleared (k := 9) (r := 277) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_277]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 278). -/
theorem data_9_278 : oddCount 278 9 = 5 ∧
    acceleratedOrbit 9 278 = 134 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_278 : gap 9 278 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_278 : threshold 9 278 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_278 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 278) = 243 * (2 * m) + 134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 278
  rw [data_9_278.1, data_9_278.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_278 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 278) = 243 * (2 * m + 1) + 134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 278
  rw [data_9_278.1, data_9_278.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_278 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 278) < 512 * (2 * m) + 278 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 278 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_278] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 278) < 512 * (2 * m) + 278 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_278 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 278) < 512 * (2 * m + 1) + 278 := by
  apply refinement_cleared (k := 9) (r := 278) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_278]; decide

end Collatz.Research.RefinementAtlas.Batch205
