import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 013. -/
namespace Collatz.Research.RefinementAtlas.Batch013
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 6). -/
theorem data_5_6 : oddCount 6 5 = 2 ∧
    acceleratedOrbit 5 6 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_6 : gap 5 6 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_6 : threshold 5 6 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_6 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 6) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 6
  rw [data_5_6.1, data_5_6.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_6 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 6) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 6
  rw [data_5_6.1, data_5_6.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_6 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 6) < 32 * (2 * m) + 6 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 6 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_6] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 6) < 32 * (2 * m) + 6 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_6 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 6) < 32 * (2 * m + 1) + 6 := by
  apply refinement_cleared (k := 5) (r := 6) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_6]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 8). -/
theorem data_5_8 : oddCount 8 5 = 1 ∧
    acceleratedOrbit 5 8 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_8 : gap 5 8 = 29 ∧ 3 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_8 : threshold 5 8 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_8 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 8) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 8
  rw [data_5_8.1, data_5_8.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_8 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 8) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 8
  rw [data_5_8.1, data_5_8.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_8 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 8) < 32 * (2 * m) + 8 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 8 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_8] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 8) < 32 * (2 * m) + 8 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_8 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 8) < 32 * (2 * m + 1) + 8 := by
  apply refinement_cleared (k := 5) (r := 8) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_8]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 10). -/
theorem data_5_10 : oddCount 10 5 = 1 ∧
    acceleratedOrbit 5 10 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_10 : gap 5 10 = 29 ∧ 3 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_10 : threshold 5 10 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_10 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 10) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 10
  rw [data_5_10.1, data_5_10.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_10 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 10) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 10
  rw [data_5_10.1, data_5_10.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_10 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 10) < 32 * (2 * m) + 10 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 10 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_10] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 10) < 32 * (2 * m) + 10 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_10 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 10) < 32 * (2 * m + 1) + 10 := by
  apply refinement_cleared (k := 5) (r := 10) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_10]; decide

end Collatz.Research.RefinementAtlas.Batch013
