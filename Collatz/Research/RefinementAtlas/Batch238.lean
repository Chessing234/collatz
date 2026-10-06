import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 238. -/
namespace Collatz.Research.RefinementAtlas.Batch238
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 402). -/
theorem data_9_402 : oddCount 402 9 = 4 ∧
    acceleratedOrbit 9 402 = 64 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_402 : gap 9 402 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_402 : threshold 9 402 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_402 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 402) = 81 * (2 * m) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 402
  rw [data_9_402.1, data_9_402.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_402 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 402) = 81 * (2 * m + 1) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 402
  rw [data_9_402.1, data_9_402.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_402 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 402) < 512 * (2 * m) + 402 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 402 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_402] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 402) < 512 * (2 * m) + 402 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_402 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 402) < 512 * (2 * m + 1) + 402 := by
  apply refinement_cleared (k := 9) (r := 402) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_402]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 403). -/
theorem data_9_403 : oddCount 403 9 = 4 ∧
    acceleratedOrbit 9 403 = 64 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_403 : gap 9 403 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_403 : threshold 9 403 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_403 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 403) = 81 * (2 * m) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 403
  rw [data_9_403.1, data_9_403.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_403 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 403) = 81 * (2 * m + 1) + 64 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 403
  rw [data_9_403.1, data_9_403.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_403 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 403) < 512 * (2 * m) + 403 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 403 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_403] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 403) < 512 * (2 * m) + 403 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_403 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 403) < 512 * (2 * m + 1) + 403 := by
  apply refinement_cleared (k := 9) (r := 403) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_403]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 404). -/
theorem data_9_404 : oddCount 404 9 = 3 ∧
    acceleratedOrbit 9 404 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_404 : gap 9 404 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_404 : threshold 9 404 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_404 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 404) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 404
  rw [data_9_404.1, data_9_404.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_404 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 404) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 404
  rw [data_9_404.1, data_9_404.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_404 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 404) < 512 * (2 * m) + 404 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 404 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_404] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 404) < 512 * (2 * m) + 404 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_404 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 404) < 512 * (2 * m + 1) + 404 := by
  apply refinement_cleared (k := 9) (r := 404) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_404]; decide

end Collatz.Research.RefinementAtlas.Batch238
