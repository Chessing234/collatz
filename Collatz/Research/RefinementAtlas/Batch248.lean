import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 248. -/
namespace Collatz.Research.RefinementAtlas.Batch248
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 440). -/
theorem data_9_440 : oddCount 440 9 = 4 ∧
    acceleratedOrbit 9 440 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_440 : gap 9 440 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_440 : threshold 9 440 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_440 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 440) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 440
  rw [data_9_440.1, data_9_440.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_440 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 440) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 440
  rw [data_9_440.1, data_9_440.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_440 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 440) < 512 * (2 * m) + 440 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 440 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_440] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 440) < 512 * (2 * m) + 440 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_440 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 440) < 512 * (2 * m + 1) + 440 := by
  apply refinement_cleared (k := 9) (r := 440) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_440]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 441). -/
theorem data_9_441 : oddCount 441 9 = 4 ∧
    acceleratedOrbit 9 441 = 70 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_441 : gap 9 441 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_441 : threshold 9 441 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_441 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 441) = 81 * (2 * m) + 70 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 441
  rw [data_9_441.1, data_9_441.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_441 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 441) = 81 * (2 * m + 1) + 70 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 441
  rw [data_9_441.1, data_9_441.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_441 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 441) < 512 * (2 * m) + 441 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 441 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_441] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 441) < 512 * (2 * m) + 441 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_441 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 441) < 512 * (2 * m + 1) + 441 := by
  apply refinement_cleared (k := 9) (r := 441) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_441]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 442). -/
theorem data_9_442 : oddCount 442 9 = 4 ∧
    acceleratedOrbit 9 442 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_442 : gap 9 442 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_442 : threshold 9 442 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_442 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 442) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 442
  rw [data_9_442.1, data_9_442.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_442 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 442) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 442
  rw [data_9_442.1, data_9_442.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_442 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 442) < 512 * (2 * m) + 442 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 442 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_442] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 442) < 512 * (2 * m) + 442 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_442 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 442) < 512 * (2 * m + 1) + 442 := by
  apply refinement_cleared (k := 9) (r := 442) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_442]; decide

end Collatz.Research.RefinementAtlas.Batch248
