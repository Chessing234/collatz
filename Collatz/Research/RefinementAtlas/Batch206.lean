import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 206. -/
namespace Collatz.Research.RefinementAtlas.Batch206
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 279). -/
theorem data_9_279 : oddCount 279 9 = 5 ∧
    acceleratedOrbit 9 279 = 134 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_279 : gap 9 279 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_279 : threshold 9 279 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_279 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 279) = 243 * (2 * m) + 134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 279
  rw [data_9_279.1, data_9_279.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_279 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 279) = 243 * (2 * m + 1) + 134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 279
  rw [data_9_279.1, data_9_279.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_279 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 279) < 512 * (2 * m) + 279 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 279 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_279] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 279) < 512 * (2 * m) + 279 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_279 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 279) < 512 * (2 * m + 1) + 279 := by
  apply refinement_cleared (k := 9) (r := 279) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_279]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 280). -/
theorem data_9_280 : oddCount 280 9 = 2 ∧
    acceleratedOrbit 9 280 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_280 : gap 9 280 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_280 : threshold 9 280 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_280 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 280) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 280
  rw [data_9_280.1, data_9_280.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_280 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 280) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 280
  rw [data_9_280.1, data_9_280.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_280 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 280) < 512 * (2 * m) + 280 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 280 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_280] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 280) < 512 * (2 * m) + 280 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_280 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 280) < 512 * (2 * m + 1) + 280 := by
  apply refinement_cleared (k := 9) (r := 280) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_280]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 282). -/
theorem data_9_282 : oddCount 282 9 = 2 ∧
    acceleratedOrbit 9 282 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_282 : gap 9 282 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_282 : threshold 9 282 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_282 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 282) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 282
  rw [data_9_282.1, data_9_282.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_282 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 282) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 282
  rw [data_9_282.1, data_9_282.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_282 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 282) < 512 * (2 * m) + 282 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 282 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_282] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 282) < 512 * (2 * m) + 282 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_282 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 282) < 512 * (2 * m + 1) + 282 := by
  apply refinement_cleared (k := 9) (r := 282) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_282]; decide

end Collatz.Research.RefinementAtlas.Batch206
