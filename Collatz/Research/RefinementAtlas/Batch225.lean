import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 225. -/
namespace Collatz.Research.RefinementAtlas.Batch225
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 355). -/
theorem data_9_355 : oddCount 355 9 = 3 ∧
    acceleratedOrbit 9 355 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_355 : gap 9 355 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_355 : threshold 9 355 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_355 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 355) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 355
  rw [data_9_355.1, data_9_355.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_355 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 355) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 355
  rw [data_9_355.1, data_9_355.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_355 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 355) < 512 * (2 * m) + 355 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 355 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_355] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 355) < 512 * (2 * m) + 355 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_355 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 355) < 512 * (2 * m + 1) + 355 := by
  apply refinement_cleared (k := 9) (r := 355) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_355]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 356). -/
theorem data_9_356 : oddCount 356 9 = 3 ∧
    acceleratedOrbit 9 356 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_356 : gap 9 356 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_356 : threshold 9 356 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_356 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 356) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 356
  rw [data_9_356.1, data_9_356.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_356 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 356) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 356
  rw [data_9_356.1, data_9_356.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_356 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 356) < 512 * (2 * m) + 356 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 356 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_356] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 356) < 512 * (2 * m) + 356 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_356 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 356) < 512 * (2 * m + 1) + 356 := by
  apply refinement_cleared (k := 9) (r := 356) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_356]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 357). -/
theorem data_9_357 : oddCount 357 9 = 3 ∧
    acceleratedOrbit 9 357 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_357 : gap 9 357 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_357 : threshold 9 357 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_357 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 357) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 357
  rw [data_9_357.1, data_9_357.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_357 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 357) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 357
  rw [data_9_357.1, data_9_357.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_357 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 357) < 512 * (2 * m) + 357 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 357 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_357] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 357) < 512 * (2 * m) + 357 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_357 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 357) < 512 * (2 * m + 1) + 357 := by
  apply refinement_cleared (k := 9) (r := 357) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_357]; decide

end Collatz.Research.RefinementAtlas.Batch225
