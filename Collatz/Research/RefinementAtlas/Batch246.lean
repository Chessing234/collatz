import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 246. -/
namespace Collatz.Research.RefinementAtlas.Batch246
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 434). -/
theorem data_9_434 : oddCount 434 9 = 3 ∧
    acceleratedOrbit 9 434 = 23 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_434 : gap 9 434 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_434 : threshold 9 434 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_434 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 434) = 27 * (2 * m) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 434
  rw [data_9_434.1, data_9_434.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_434 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 434) = 27 * (2 * m + 1) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 434
  rw [data_9_434.1, data_9_434.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_434 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 434) < 512 * (2 * m) + 434 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 434 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_434] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 434) < 512 * (2 * m) + 434 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_434 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 434) < 512 * (2 * m + 1) + 434 := by
  apply refinement_cleared (k := 9) (r := 434) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_434]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 435). -/
theorem data_9_435 : oddCount 435 9 = 3 ∧
    acceleratedOrbit 9 435 = 23 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_435 : gap 9 435 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_435 : threshold 9 435 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_435 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 435) = 27 * (2 * m) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 435
  rw [data_9_435.1, data_9_435.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_435 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 435) = 27 * (2 * m + 1) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 435
  rw [data_9_435.1, data_9_435.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_435 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 435) < 512 * (2 * m) + 435 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 435 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_435] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 435) < 512 * (2 * m) + 435 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_435 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 435) < 512 * (2 * m + 1) + 435 := by
  apply refinement_cleared (k := 9) (r := 435) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_435]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 436). -/
theorem data_9_436 : oddCount 436 9 = 4 ∧
    acceleratedOrbit 9 436 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_436 : gap 9 436 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_436 : threshold 9 436 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_436 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 436) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 436
  rw [data_9_436.1, data_9_436.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_436 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 436) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 436
  rw [data_9_436.1, data_9_436.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_436 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 436) < 512 * (2 * m) + 436 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 436 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_436] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 436) < 512 * (2 * m) + 436 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_436 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 436) < 512 * (2 * m + 1) + 436 := by
  apply refinement_cleared (k := 9) (r := 436) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_436]; decide

end Collatz.Research.RefinementAtlas.Batch246
