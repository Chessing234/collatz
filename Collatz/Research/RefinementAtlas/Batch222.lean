import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 222. -/
namespace Collatz.Research.RefinementAtlas.Batch222
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 344). -/
theorem data_9_344 : oddCount 344 9 = 4 ∧
    acceleratedOrbit 9 344 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_344 : gap 9 344 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_344 : threshold 9 344 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_344 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 344) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 344
  rw [data_9_344.1, data_9_344.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_344 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 344) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 344
  rw [data_9_344.1, data_9_344.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_344 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 344) < 512 * (2 * m) + 344 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 344 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_344] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 344) < 512 * (2 * m) + 344 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_344 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 344) < 512 * (2 * m + 1) + 344 := by
  apply refinement_cleared (k := 9) (r := 344) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_344]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 345). -/
theorem data_9_345 : oddCount 345 9 = 4 ∧
    acceleratedOrbit 9 345 = 55 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_345 : gap 9 345 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_345 : threshold 9 345 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_345 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 345) = 81 * (2 * m) + 55 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 345
  rw [data_9_345.1, data_9_345.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_345 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 345) = 81 * (2 * m + 1) + 55 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 345
  rw [data_9_345.1, data_9_345.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_345 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 345) < 512 * (2 * m) + 345 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 345 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_345] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 345) < 512 * (2 * m) + 345 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_345 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 345) < 512 * (2 * m + 1) + 345 := by
  apply refinement_cleared (k := 9) (r := 345) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_345]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 346). -/
theorem data_9_346 : oddCount 346 9 = 4 ∧
    acceleratedOrbit 9 346 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_346 : gap 9 346 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_346 : threshold 9 346 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_346 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 346) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 346
  rw [data_9_346.1, data_9_346.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_346 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 346) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 346
  rw [data_9_346.1, data_9_346.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_346 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 346) < 512 * (2 * m) + 346 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 346 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_346] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 346) < 512 * (2 * m) + 346 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_346 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 346) < 512 * (2 * m + 1) + 346 := by
  apply refinement_cleared (k := 9) (r := 346) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_346]; decide

end Collatz.Research.RefinementAtlas.Batch222
