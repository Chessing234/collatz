import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 250. -/
namespace Collatz.Research.RefinementAtlas.Batch250
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 452). -/
theorem data_9_452 : oddCount 452 9 = 2 ∧
    acceleratedOrbit 9 452 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_452 : gap 9 452 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_452 : threshold 9 452 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_452 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 452) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 452
  rw [data_9_452.1, data_9_452.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_452 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 452) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 452
  rw [data_9_452.1, data_9_452.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_452 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 452) < 512 * (2 * m) + 452 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 452 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_452] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 452) < 512 * (2 * m) + 452 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_452 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 452) < 512 * (2 * m + 1) + 452 := by
  apply refinement_cleared (k := 9) (r := 452) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_452]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 453). -/
theorem data_9_453 : oddCount 453 9 = 2 ∧
    acceleratedOrbit 9 453 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_453 : gap 9 453 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_453 : threshold 9 453 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_453 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 453) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 453
  rw [data_9_453.1, data_9_453.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_453 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 453) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 453
  rw [data_9_453.1, data_9_453.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_453 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 453) < 512 * (2 * m) + 453 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 453 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_453] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 453) < 512 * (2 * m) + 453 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_453 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 453) < 512 * (2 * m + 1) + 453 := by
  apply refinement_cleared (k := 9) (r := 453) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_453]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 454). -/
theorem data_9_454 : oddCount 454 9 = 2 ∧
    acceleratedOrbit 9 454 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_454 : gap 9 454 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_454 : threshold 9 454 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_454 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 454) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 454
  rw [data_9_454.1, data_9_454.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_454 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 454) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 454
  rw [data_9_454.1, data_9_454.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_454 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 454) < 512 * (2 * m) + 454 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 454 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_454] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 454) < 512 * (2 * m) + 454 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_454 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 454) < 512 * (2 * m + 1) + 454 := by
  apply refinement_cleared (k := 9) (r := 454) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_454]; decide

end Collatz.Research.RefinementAtlas.Batch250
