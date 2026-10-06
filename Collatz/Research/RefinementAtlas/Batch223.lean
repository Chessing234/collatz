import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 223. -/
namespace Collatz.Research.RefinementAtlas.Batch223
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 348). -/
theorem data_9_348 : oddCount 348 9 = 4 ∧
    acceleratedOrbit 9 348 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_348 : gap 9 348 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_348 : threshold 9 348 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_348 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 348) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 348
  rw [data_9_348.1, data_9_348.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_348 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 348) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 348
  rw [data_9_348.1, data_9_348.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_348 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 348) < 512 * (2 * m) + 348 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 348 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_348] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 348) < 512 * (2 * m) + 348 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_348 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 348) < 512 * (2 * m + 1) + 348 := by
  apply refinement_cleared (k := 9) (r := 348) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_348]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 349). -/
theorem data_9_349 : oddCount 349 9 = 4 ∧
    acceleratedOrbit 9 349 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_349 : gap 9 349 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_349 : threshold 9 349 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_349 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 349) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 349
  rw [data_9_349.1, data_9_349.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_349 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 349) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 349
  rw [data_9_349.1, data_9_349.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_349 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 349) < 512 * (2 * m) + 349 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 349 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_349] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 349) < 512 * (2 * m) + 349 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_349 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 349) < 512 * (2 * m + 1) + 349 := by
  apply refinement_cleared (k := 9) (r := 349) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_349]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 350). -/
theorem data_9_350 : oddCount 350 9 = 5 ∧
    acceleratedOrbit 9 350 = 167 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_350 : gap 9 350 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_350 : threshold 9 350 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_350 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 350) = 243 * (2 * m) + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 350
  rw [data_9_350.1, data_9_350.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_350 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 350) = 243 * (2 * m + 1) + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 350
  rw [data_9_350.1, data_9_350.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_350 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 350) < 512 * (2 * m) + 350 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 350 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_350] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 350) < 512 * (2 * m) + 350 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_350 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 350) < 512 * (2 * m + 1) + 350 := by
  apply refinement_cleared (k := 9) (r := 350) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_350]; decide

end Collatz.Research.RefinementAtlas.Batch223
