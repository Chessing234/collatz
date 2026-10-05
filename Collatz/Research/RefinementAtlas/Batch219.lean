import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 219. -/
namespace Collatz.Research.RefinementAtlas.Batch219
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 330). -/
theorem data_9_330 : oddCount 330 9 = 5 ∧
    acceleratedOrbit 9 330 = 161 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_330 : gap 9 330 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_330 : threshold 9 330 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_330 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 330) = 243 * (2 * m) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 330
  rw [data_9_330.1, data_9_330.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_330 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 330) = 243 * (2 * m + 1) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 330
  rw [data_9_330.1, data_9_330.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_330 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 330) < 512 * (2 * m) + 330 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 330 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_330] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 330) < 512 * (2 * m) + 330 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_330 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 330) < 512 * (2 * m + 1) + 330 := by
  apply refinement_cleared (k := 9) (r := 330) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_330]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 331). -/
theorem data_9_331 : oddCount 331 9 = 4 ∧
    acceleratedOrbit 9 331 = 53 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_331 : gap 9 331 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_331 : threshold 9 331 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_331 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 331) = 81 * (2 * m) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 331
  rw [data_9_331.1, data_9_331.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_331 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 331) = 81 * (2 * m + 1) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 331
  rw [data_9_331.1, data_9_331.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_331 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 331) < 512 * (2 * m) + 331 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 331 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_331] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 331) < 512 * (2 * m) + 331 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_331 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 331) < 512 * (2 * m + 1) + 331 := by
  apply refinement_cleared (k := 9) (r := 331) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_331]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 332). -/
theorem data_9_332 : oddCount 332 9 = 5 ∧
    acceleratedOrbit 9 332 = 161 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_332 : gap 9 332 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_332 : threshold 9 332 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_332 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 332) = 243 * (2 * m) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 332
  rw [data_9_332.1, data_9_332.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_332 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 332) = 243 * (2 * m + 1) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 332
  rw [data_9_332.1, data_9_332.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_332 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 332) < 512 * (2 * m) + 332 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 332 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_332] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 332) < 512 * (2 * m) + 332 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_332 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 332) < 512 * (2 * m + 1) + 332 := by
  apply refinement_cleared (k := 9) (r := 332) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_332]; decide

end Collatz.Research.RefinementAtlas.Batch219
