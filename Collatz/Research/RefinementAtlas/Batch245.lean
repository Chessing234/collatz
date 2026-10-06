import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 245. -/
namespace Collatz.Research.RefinementAtlas.Batch245
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 431). -/
theorem data_9_431 : oddCount 431 9 = 5 ∧
    acceleratedOrbit 9 431 = 205 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_431 : gap 9 431 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_431 : threshold 9 431 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_431 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 431) = 243 * (2 * m) + 205 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 431
  rw [data_9_431.1, data_9_431.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_431 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 431) = 243 * (2 * m + 1) + 205 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 431
  rw [data_9_431.1, data_9_431.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_431 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 431) < 512 * (2 * m) + 431 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 431 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_431] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 431) < 512 * (2 * m) + 431 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_431 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 431) < 512 * (2 * m + 1) + 431 := by
  apply refinement_cleared (k := 9) (r := 431) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_431]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 432). -/
theorem data_9_432 : oddCount 432 9 = 4 ∧
    acceleratedOrbit 9 432 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_432 : gap 9 432 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_432 : threshold 9 432 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_432 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 432) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 432
  rw [data_9_432.1, data_9_432.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_432 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 432) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 432
  rw [data_9_432.1, data_9_432.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_432 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 432) < 512 * (2 * m) + 432 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 432 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_432] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 432) < 512 * (2 * m) + 432 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_432 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 432) < 512 * (2 * m + 1) + 432 := by
  apply refinement_cleared (k := 9) (r := 432) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_432]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 433). -/
theorem data_9_433 : oddCount 433 9 = 3 ∧
    acceleratedOrbit 9 433 = 23 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_433 : gap 9 433 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_433 : threshold 9 433 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_433 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 433) = 27 * (2 * m) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 433
  rw [data_9_433.1, data_9_433.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_433 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 433) = 27 * (2 * m + 1) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 433
  rw [data_9_433.1, data_9_433.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_433 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 433) < 512 * (2 * m) + 433 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 433 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_433] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 433) < 512 * (2 * m) + 433 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_433 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 433) < 512 * (2 * m + 1) + 433 := by
  apply refinement_cleared (k := 9) (r := 433) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_433]; decide

end Collatz.Research.RefinementAtlas.Batch245
