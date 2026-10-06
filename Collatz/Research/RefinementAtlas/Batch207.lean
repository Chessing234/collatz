import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 207. -/
namespace Collatz.Research.RefinementAtlas.Batch207
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 284). -/
theorem data_9_284 : oddCount 284 9 = 5 ∧
    acceleratedOrbit 9 284 = 137 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_284 : gap 9 284 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_284 : threshold 9 284 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_284 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 284) = 243 * (2 * m) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 284
  rw [data_9_284.1, data_9_284.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_284 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 284) = 243 * (2 * m + 1) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 284
  rw [data_9_284.1, data_9_284.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_284 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 284) < 512 * (2 * m) + 284 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 284 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_284] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 284) < 512 * (2 * m) + 284 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_284 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 284) < 512 * (2 * m + 1) + 284 := by
  apply refinement_cleared (k := 9) (r := 284) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_284]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 285). -/
theorem data_9_285 : oddCount 285 9 = 5 ∧
    acceleratedOrbit 9 285 = 137 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_285 : gap 9 285 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_285 : threshold 9 285 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_285 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 285) = 243 * (2 * m) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 285
  rw [data_9_285.1, data_9_285.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_285 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 285) = 243 * (2 * m + 1) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 285
  rw [data_9_285.1, data_9_285.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_285 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 285) < 512 * (2 * m) + 285 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 285 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_285] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 285) < 512 * (2 * m) + 285 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_285 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 285) < 512 * (2 * m + 1) + 285 := by
  apply refinement_cleared (k := 9) (r := 285) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_285]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 286). -/
theorem data_9_286 : oddCount 286 9 = 5 ∧
    acceleratedOrbit 9 286 = 137 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_286 : gap 9 286 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_286 : threshold 9 286 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_286 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 286) = 243 * (2 * m) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 286
  rw [data_9_286.1, data_9_286.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_286 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 286) = 243 * (2 * m + 1) + 137 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 286
  rw [data_9_286.1, data_9_286.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_286 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 286) < 512 * (2 * m) + 286 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 286 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_286] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 286) < 512 * (2 * m) + 286 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_286 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 286) < 512 * (2 * m + 1) + 286 := by
  apply refinement_cleared (k := 9) (r := 286) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_286]; decide

end Collatz.Research.RefinementAtlas.Batch207
