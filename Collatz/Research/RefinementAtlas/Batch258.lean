import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 258. -/
namespace Collatz.Research.RefinementAtlas.Batch258
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 486). -/
theorem data_9_486 : oddCount 486 9 = 5 ∧
    acceleratedOrbit 9 486 = 233 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_486 : gap 9 486 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_486 : threshold 9 486 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_486 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 486) = 243 * (2 * m) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 486
  rw [data_9_486.1, data_9_486.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_486 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 486) = 243 * (2 * m + 1) + 233 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 486
  rw [data_9_486.1, data_9_486.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_486 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 486) < 512 * (2 * m) + 486 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 486 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_486] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 486) < 512 * (2 * m) + 486 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_486 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 486) < 512 * (2 * m + 1) + 486 := by
  apply refinement_cleared (k := 9) (r := 486) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_486]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 488). -/
theorem data_9_488 : oddCount 488 9 = 4 ∧
    acceleratedOrbit 9 488 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_488 : gap 9 488 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_488 : threshold 9 488 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_488 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 488) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 488
  rw [data_9_488.1, data_9_488.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_488 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 488) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 488
  rw [data_9_488.1, data_9_488.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_488 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 488) < 512 * (2 * m) + 488 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 488 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_488] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 488) < 512 * (2 * m) + 488 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_488 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 488) < 512 * (2 * m + 1) + 488 := by
  apply refinement_cleared (k := 9) (r := 488) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_488]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 490). -/
theorem data_9_490 : oddCount 490 9 = 4 ∧
    acceleratedOrbit 9 490 = 80 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_490 : gap 9 490 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_490 : threshold 9 490 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_490 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 490) = 81 * (2 * m) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 490
  rw [data_9_490.1, data_9_490.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_490 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 490) = 81 * (2 * m + 1) + 80 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 490
  rw [data_9_490.1, data_9_490.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_490 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 490) < 512 * (2 * m) + 490 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 490 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_490] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 490) < 512 * (2 * m) + 490 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_490 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 490) < 512 * (2 * m + 1) + 490 := by
  apply refinement_cleared (k := 9) (r := 490) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_490]; decide

end Collatz.Research.RefinementAtlas.Batch258
