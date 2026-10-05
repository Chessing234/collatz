import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 216. -/
namespace Collatz.Research.RefinementAtlas.Batch216
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 320). -/
theorem data_9_320 : oddCount 320 9 = 1 ∧
    acceleratedOrbit 9 320 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_320 : gap 9 320 = 509 ∧ 3 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_320 : threshold 9 320 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_320 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 320) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 320
  rw [data_9_320.1, data_9_320.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_320 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 320) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 320
  rw [data_9_320.1, data_9_320.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_320 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 320) < 512 * (2 * m) + 320 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 320 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_320] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 320) < 512 * (2 * m) + 320 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_320 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 320) < 512 * (2 * m + 1) + 320 := by
  apply refinement_cleared (k := 9) (r := 320) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_320]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 321). -/
theorem data_9_321 : oddCount 321 9 = 3 ∧
    acceleratedOrbit 9 321 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_321 : gap 9 321 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_321 : threshold 9 321 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_321 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 321) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 321
  rw [data_9_321.1, data_9_321.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_321 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 321) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 321
  rw [data_9_321.1, data_9_321.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_321 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 321) < 512 * (2 * m) + 321 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 321 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_321] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 321) < 512 * (2 * m) + 321 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_321 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 321) < 512 * (2 * m + 1) + 321 := by
  apply refinement_cleared (k := 9) (r := 321) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_321]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 322). -/
theorem data_9_322 : oddCount 322 9 = 5 ∧
    acceleratedOrbit 9 322 = 155 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_322 : gap 9 322 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_322 : threshold 9 322 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_322 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 322) = 243 * (2 * m) + 155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 322
  rw [data_9_322.1, data_9_322.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_322 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 322) = 243 * (2 * m + 1) + 155 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 322
  rw [data_9_322.1, data_9_322.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_322 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 322) < 512 * (2 * m) + 322 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 322 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_322] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 322) < 512 * (2 * m) + 322 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_322 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 322) < 512 * (2 * m + 1) + 322 := by
  apply refinement_cleared (k := 9) (r := 322) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_322]; decide

end Collatz.Research.RefinementAtlas.Batch216
