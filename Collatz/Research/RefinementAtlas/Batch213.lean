import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 213. -/
namespace Collatz.Research.RefinementAtlas.Batch213
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 306). -/
theorem data_9_306 : oddCount 306 9 = 4 ∧
    acceleratedOrbit 9 306 = 49 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_306 : gap 9 306 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_306 : threshold 9 306 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_306 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 306) = 81 * (2 * m) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 306
  rw [data_9_306.1, data_9_306.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_306 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 306) = 81 * (2 * m + 1) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 306
  rw [data_9_306.1, data_9_306.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_306 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 306) < 512 * (2 * m) + 306 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 306 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_306] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 306) < 512 * (2 * m) + 306 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_306 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 306) < 512 * (2 * m + 1) + 306 := by
  apply refinement_cleared (k := 9) (r := 306) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_306]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 307). -/
theorem data_9_307 : oddCount 307 9 = 4 ∧
    acceleratedOrbit 9 307 = 49 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_307 : gap 9 307 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_307 : threshold 9 307 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_307 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 307) = 81 * (2 * m) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 307
  rw [data_9_307.1, data_9_307.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_307 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 307) = 81 * (2 * m + 1) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 307
  rw [data_9_307.1, data_9_307.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_307 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 307) < 512 * (2 * m) + 307 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 307 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_307] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 307) < 512 * (2 * m) + 307 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_307 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 307) < 512 * (2 * m + 1) + 307 := by
  apply refinement_cleared (k := 9) (r := 307) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_307]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 308). -/
theorem data_9_308 : oddCount 308 9 = 3 ∧
    acceleratedOrbit 9 308 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_308 : gap 9 308 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_308 : threshold 9 308 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_308 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 308) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 308
  rw [data_9_308.1, data_9_308.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_308 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 308) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 308
  rw [data_9_308.1, data_9_308.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_308 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 308) < 512 * (2 * m) + 308 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 308 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_308] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 308) < 512 * (2 * m) + 308 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_308 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 308) < 512 * (2 * m + 1) + 308 := by
  apply refinement_cleared (k := 9) (r := 308) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_308]; decide

end Collatz.Research.RefinementAtlas.Batch213
