import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 251. -/
namespace Collatz.Research.RefinementAtlas.Batch251
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 456). -/
theorem data_9_456 : oddCount 456 9 = 4 ∧
    acceleratedOrbit 9 456 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_456 : gap 9 456 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_456 : threshold 9 456 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_456 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 456) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 456
  rw [data_9_456.1, data_9_456.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_456 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 456) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 456
  rw [data_9_456.1, data_9_456.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_456 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 456) < 512 * (2 * m) + 456 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 456 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_456] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 456) < 512 * (2 * m) + 456 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_456 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 456) < 512 * (2 * m + 1) + 456 := by
  apply refinement_cleared (k := 9) (r := 456) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_456]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 457). -/
theorem data_9_457 : oddCount 457 9 = 5 ∧
    acceleratedOrbit 9 457 = 218 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_457 : gap 9 457 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_457 : threshold 9 457 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_457 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 457) = 243 * (2 * m) + 218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 457
  rw [data_9_457.1, data_9_457.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_457 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 457) = 243 * (2 * m + 1) + 218 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 457
  rw [data_9_457.1, data_9_457.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_457 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 457) < 512 * (2 * m) + 457 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 457 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_457] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 457) < 512 * (2 * m) + 457 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_457 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 457) < 512 * (2 * m + 1) + 457 := by
  apply refinement_cleared (k := 9) (r := 457) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_457]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 458). -/
theorem data_9_458 : oddCount 458 9 = 4 ∧
    acceleratedOrbit 9 458 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_458 : gap 9 458 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_458 : threshold 9 458 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_458 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 458) = 81 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 458
  rw [data_9_458.1, data_9_458.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_458 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 458) = 81 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 458
  rw [data_9_458.1, data_9_458.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_458 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 458) < 512 * (2 * m) + 458 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 458 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_458] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 458) < 512 * (2 * m) + 458 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_458 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 458) < 512 * (2 * m + 1) + 458 := by
  apply refinement_cleared (k := 9) (r := 458) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_458]; decide

end Collatz.Research.RefinementAtlas.Batch251
