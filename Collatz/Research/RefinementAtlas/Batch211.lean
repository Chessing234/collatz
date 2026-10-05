import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 211. -/
namespace Collatz.Research.RefinementAtlas.Batch211
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 299). -/
theorem data_9_299 : oddCount 299 9 = 5 ∧
    acceleratedOrbit 9 299 = 143 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_299 : gap 9 299 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_299 : threshold 9 299 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_299 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 299) = 243 * (2 * m) + 143 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 299
  rw [data_9_299.1, data_9_299.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_299 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 299) = 243 * (2 * m + 1) + 143 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 299
  rw [data_9_299.1, data_9_299.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_299 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 299) < 512 * (2 * m) + 299 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 299 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_299] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 299) < 512 * (2 * m) + 299 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_299 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 299) < 512 * (2 * m + 1) + 299 := by
  apply refinement_cleared (k := 9) (r := 299) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_299]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 300). -/
theorem data_9_300 : oddCount 300 9 = 3 ∧
    acceleratedOrbit 9 300 = 16 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_300 : gap 9 300 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_300 : threshold 9 300 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_300 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 300) = 27 * (2 * m) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 300
  rw [data_9_300.1, data_9_300.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_300 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 300) = 27 * (2 * m + 1) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 300
  rw [data_9_300.1, data_9_300.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_300 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 300) < 512 * (2 * m) + 300 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 300 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_300] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 300) < 512 * (2 * m) + 300 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_300 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 300) < 512 * (2 * m + 1) + 300 := by
  apply refinement_cleared (k := 9) (r := 300) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_300]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 301). -/
theorem data_9_301 : oddCount 301 9 = 3 ∧
    acceleratedOrbit 9 301 = 16 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_301 : gap 9 301 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_301 : threshold 9 301 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_301 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 301) = 27 * (2 * m) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 301
  rw [data_9_301.1, data_9_301.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_301 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 301) = 27 * (2 * m + 1) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 301
  rw [data_9_301.1, data_9_301.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_301 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 301) < 512 * (2 * m) + 301 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 301 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_301] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 301) < 512 * (2 * m) + 301 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_301 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 301) < 512 * (2 * m + 1) + 301 := by
  apply refinement_cleared (k := 9) (r := 301) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_301]; decide

end Collatz.Research.RefinementAtlas.Batch211
