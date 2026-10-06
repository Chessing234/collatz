import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 228. -/
namespace Collatz.Research.RefinementAtlas.Batch228
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 365). -/
theorem data_9_365 : oddCount 365 9 = 5 ∧
    acceleratedOrbit 9 365 = 175 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_365 : gap 9 365 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_365 : threshold 9 365 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_365 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 365) = 243 * (2 * m) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 365
  rw [data_9_365.1, data_9_365.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_365 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 365) = 243 * (2 * m + 1) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 365
  rw [data_9_365.1, data_9_365.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_365 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 365) < 512 * (2 * m) + 365 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 365 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_365] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 365) < 512 * (2 * m) + 365 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_365 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 365) < 512 * (2 * m + 1) + 365 := by
  apply refinement_cleared (k := 9) (r := 365) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_365]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 366). -/
theorem data_9_366 : oddCount 366 9 = 5 ∧
    acceleratedOrbit 9 366 = 175 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_366 : gap 9 366 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_366 : threshold 9 366 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_366 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 366) = 243 * (2 * m) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 366
  rw [data_9_366.1, data_9_366.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_366 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 366) = 243 * (2 * m + 1) + 175 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 366
  rw [data_9_366.1, data_9_366.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_366 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 366) < 512 * (2 * m) + 366 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 366 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_366] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 366) < 512 * (2 * m) + 366 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_366 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 366) < 512 * (2 * m + 1) + 366 := by
  apply refinement_cleared (k := 9) (r := 366) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_366]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 368). -/
theorem data_9_368 : oddCount 368 9 = 3 ∧
    acceleratedOrbit 9 368 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_368 : gap 9 368 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_368 : threshold 9 368 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_368 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 368) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 368
  rw [data_9_368.1, data_9_368.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_368 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 368) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 368
  rw [data_9_368.1, data_9_368.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_368 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 368) < 512 * (2 * m) + 368 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 368 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_368] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 368) < 512 * (2 * m) + 368 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_368 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 368) < 512 * (2 * m + 1) + 368 := by
  apply refinement_cleared (k := 9) (r := 368) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_368]; decide

end Collatz.Research.RefinementAtlas.Batch228
