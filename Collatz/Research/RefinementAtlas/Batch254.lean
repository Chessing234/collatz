import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 254. -/
namespace Collatz.Research.RefinementAtlas.Batch254
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 469). -/
theorem data_9_469 : oddCount 469 9 = 3 ∧
    acceleratedOrbit 9 469 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_469 : gap 9 469 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_469 : threshold 9 469 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_469 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 469) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 469
  rw [data_9_469.1, data_9_469.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_469 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 469) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 469
  rw [data_9_469.1, data_9_469.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_469 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 469) < 512 * (2 * m) + 469 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 469 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_469] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 469) < 512 * (2 * m) + 469 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_469 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 469) < 512 * (2 * m + 1) + 469 := by
  apply refinement_cleared (k := 9) (r := 469) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_469]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 472). -/
theorem data_9_472 : oddCount 472 9 = 4 ∧
    acceleratedOrbit 9 472 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_472 : gap 9 472 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_472 : threshold 9 472 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_472 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 472) = 81 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 472
  rw [data_9_472.1, data_9_472.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_472 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 472) = 81 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 472
  rw [data_9_472.1, data_9_472.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_472 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 472) < 512 * (2 * m) + 472 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 472 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_472] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 472) < 512 * (2 * m) + 472 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_472 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 472) < 512 * (2 * m + 1) + 472 := by
  apply refinement_cleared (k := 9) (r := 472) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_472]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 473). -/
theorem data_9_473 : oddCount 473 9 = 3 ∧
    acceleratedOrbit 9 473 = 25 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_473 : gap 9 473 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_473 : threshold 9 473 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_473 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 473) = 27 * (2 * m) + 25 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 473
  rw [data_9_473.1, data_9_473.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_473 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 473) = 27 * (2 * m + 1) + 25 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 473
  rw [data_9_473.1, data_9_473.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_473 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 473) < 512 * (2 * m) + 473 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 473 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_473] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 473) < 512 * (2 * m) + 473 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_473 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 473) < 512 * (2 * m + 1) + 473 := by
  apply refinement_cleared (k := 9) (r := 473) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_473]; decide

end Collatz.Research.RefinementAtlas.Batch254
