import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 215. -/
namespace Collatz.Research.RefinementAtlas.Batch215
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 315). -/
theorem data_9_315 : oddCount 315 9 = 4 ∧
    acceleratedOrbit 9 315 = 50 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_315 : gap 9 315 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_315 : threshold 9 315 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_315 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 315) = 81 * (2 * m) + 50 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 315
  rw [data_9_315.1, data_9_315.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_315 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 315) = 81 * (2 * m + 1) + 50 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 315
  rw [data_9_315.1, data_9_315.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_315 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 315) < 512 * (2 * m) + 315 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 315 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_315] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 315) < 512 * (2 * m) + 315 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_315 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 315) < 512 * (2 * m + 1) + 315 := by
  apply refinement_cleared (k := 9) (r := 315) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_315]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 316). -/
theorem data_9_316 : oddCount 316 9 = 5 ∧
    acceleratedOrbit 9 316 = 152 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_316 : gap 9 316 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_316 : threshold 9 316 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_316 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 316) = 243 * (2 * m) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 316
  rw [data_9_316.1, data_9_316.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_316 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 316) = 243 * (2 * m + 1) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 316
  rw [data_9_316.1, data_9_316.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_316 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 316) < 512 * (2 * m) + 316 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 316 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_316] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 316) < 512 * (2 * m) + 316 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_316 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 316) < 512 * (2 * m + 1) + 316 := by
  apply refinement_cleared (k := 9) (r := 316) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_316]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 317). -/
theorem data_9_317 : oddCount 317 9 = 5 ∧
    acceleratedOrbit 9 317 = 152 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_317 : gap 9 317 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_317 : threshold 9 317 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_317 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 317) = 243 * (2 * m) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 317
  rw [data_9_317.1, data_9_317.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_317 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 317) = 243 * (2 * m + 1) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 317
  rw [data_9_317.1, data_9_317.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_317 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 317) < 512 * (2 * m) + 317 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 317 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_317] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 317) < 512 * (2 * m) + 317 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_317 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 317) < 512 * (2 * m + 1) + 317 := by
  apply refinement_cleared (k := 9) (r := 317) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_317]; decide

end Collatz.Research.RefinementAtlas.Batch215
