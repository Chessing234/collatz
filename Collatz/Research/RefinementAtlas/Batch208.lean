import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 208. -/
namespace Collatz.Research.RefinementAtlas.Batch208
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 288). -/
theorem data_9_288 : oddCount 288 9 = 3 ∧
    acceleratedOrbit 9 288 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_288 : gap 9 288 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_288 : threshold 9 288 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_288 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 288) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 288
  rw [data_9_288.1, data_9_288.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_288 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 288) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 288
  rw [data_9_288.1, data_9_288.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_288 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 288) < 512 * (2 * m) + 288 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 288 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_288] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 288) < 512 * (2 * m) + 288 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_288 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 288) < 512 * (2 * m + 1) + 288 := by
  apply refinement_cleared (k := 9) (r := 288) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_288]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 289). -/
theorem data_9_289 : oddCount 289 9 = 4 ∧
    acceleratedOrbit 9 289 = 46 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_289 : gap 9 289 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_289 : threshold 9 289 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_289 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 289) = 81 * (2 * m) + 46 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 289
  rw [data_9_289.1, data_9_289.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_289 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 289) = 81 * (2 * m + 1) + 46 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 289
  rw [data_9_289.1, data_9_289.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_289 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 289) < 512 * (2 * m) + 289 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 289 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_289] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 289) < 512 * (2 * m) + 289 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_289 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 289) < 512 * (2 * m + 1) + 289 := by
  apply refinement_cleared (k := 9) (r := 289) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_289]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 290). -/
theorem data_9_290 : oddCount 290 9 = 4 ∧
    acceleratedOrbit 9 290 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_290 : gap 9 290 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_290 : threshold 9 290 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_290 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 290) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 290
  rw [data_9_290.1, data_9_290.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_290 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 290) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 290
  rw [data_9_290.1, data_9_290.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_290 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 290) < 512 * (2 * m) + 290 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 290 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_290] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 290) < 512 * (2 * m) + 290 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_290 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 290) < 512 * (2 * m + 1) + 290 := by
  apply refinement_cleared (k := 9) (r := 290) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_290]; decide

end Collatz.Research.RefinementAtlas.Batch208
