import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 209. -/
namespace Collatz.Research.RefinementAtlas.Batch209
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 291). -/
theorem data_9_291 : oddCount 291 9 = 4 ∧
    acceleratedOrbit 9 291 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_291 : gap 9 291 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_291 : threshold 9 291 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_291 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 291) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 291
  rw [data_9_291.1, data_9_291.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_291 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 291) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 291
  rw [data_9_291.1, data_9_291.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_291 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 291) < 512 * (2 * m) + 291 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 291 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_291] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 291) < 512 * (2 * m) + 291 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_291 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 291) < 512 * (2 * m + 1) + 291 := by
  apply refinement_cleared (k := 9) (r := 291) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_291]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 292). -/
theorem data_9_292 : oddCount 292 9 = 4 ∧
    acceleratedOrbit 9 292 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_292 : gap 9 292 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_292 : threshold 9 292 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_292 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 292) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 292
  rw [data_9_292.1, data_9_292.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_292 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 292) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 292
  rw [data_9_292.1, data_9_292.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_292 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 292) < 512 * (2 * m) + 292 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 292 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_292] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 292) < 512 * (2 * m) + 292 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_292 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 292) < 512 * (2 * m + 1) + 292 := by
  apply refinement_cleared (k := 9) (r := 292) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_292]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 293). -/
theorem data_9_293 : oddCount 293 9 = 4 ∧
    acceleratedOrbit 9 293 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_293 : gap 9 293 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_293 : threshold 9 293 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_293 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 293) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 293
  rw [data_9_293.1, data_9_293.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_293 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 293) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 293
  rw [data_9_293.1, data_9_293.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_293 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 293) < 512 * (2 * m) + 293 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 293 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_293] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 293) < 512 * (2 * m) + 293 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_293 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 293) < 512 * (2 * m + 1) + 293 := by
  apply refinement_cleared (k := 9) (r := 293) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_293]; decide

end Collatz.Research.RefinementAtlas.Batch209
