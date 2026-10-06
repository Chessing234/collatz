import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 021. -/
namespace Collatz.Research.RefinementAtlas.Batch021
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 8). -/
theorem data_6_8 : oddCount 8 6 = 2 ∧
    acceleratedOrbit 6 8 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_8 : gap 6 8 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_8 : threshold 6 8 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_8 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 8) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 8
  rw [data_6_8.1, data_6_8.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_8 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 8) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 8
  rw [data_6_8.1, data_6_8.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_8 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 8) < 64 * (2 * m) + 8 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 8 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_8] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 8) < 64 * (2 * m) + 8 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_8 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 8) < 64 * (2 * m + 1) + 8 := by
  apply refinement_cleared (k := 6) (r := 8) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_8]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 10). -/
theorem data_6_10 : oddCount 10 6 = 2 ∧
    acceleratedOrbit 6 10 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_10 : gap 6 10 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_10 : threshold 6 10 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_10 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 10) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 10
  rw [data_6_10.1, data_6_10.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_10 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 10) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 10
  rw [data_6_10.1, data_6_10.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_10 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 10) < 64 * (2 * m) + 10 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 10 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_10] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 10) < 64 * (2 * m) + 10 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_10 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 10) < 64 * (2 * m + 1) + 10 := by
  apply refinement_cleared (k := 6) (r := 10) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_10]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 11). -/
theorem data_6_11 : oddCount 11 6 = 3 ∧
    acceleratedOrbit 6 11 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_11 : gap 6 11 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_11 : threshold 6 11 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_11 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 11) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 11
  rw [data_6_11.1, data_6_11.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_11 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 11) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 11
  rw [data_6_11.1, data_6_11.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_11 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 11) < 64 * (2 * m) + 11 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 11 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_11] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 11) < 64 * (2 * m) + 11 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_11 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 11) < 64 * (2 * m + 1) + 11 := by
  apply refinement_cleared (k := 6) (r := 11) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_11]; decide

end Collatz.Research.RefinementAtlas.Batch021
