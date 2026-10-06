import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 022. -/
namespace Collatz.Research.RefinementAtlas.Batch022
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 12). -/
theorem data_6_12 : oddCount 12 6 = 2 ∧
    acceleratedOrbit 6 12 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_12 : gap 6 12 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_12 : threshold 6 12 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_12 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 12) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 12
  rw [data_6_12.1, data_6_12.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_12 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 12) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 12
  rw [data_6_12.1, data_6_12.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_12 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 12) < 64 * (2 * m) + 12 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 12 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_12] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 12) < 64 * (2 * m) + 12 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_12 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 12) < 64 * (2 * m + 1) + 12 := by
  apply refinement_cleared (k := 6) (r := 12) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_12]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 13). -/
theorem data_6_13 : oddCount 13 6 = 2 ∧
    acceleratedOrbit 6 13 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_13 : gap 6 13 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_13 : threshold 6 13 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_13 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 13) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 13
  rw [data_6_13.1, data_6_13.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_13 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 13) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 13
  rw [data_6_13.1, data_6_13.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_13 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 13) < 64 * (2 * m) + 13 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 13 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_13] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 13) < 64 * (2 * m) + 13 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_13 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 13) < 64 * (2 * m + 1) + 13 := by
  apply refinement_cleared (k := 6) (r := 13) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_13]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 16). -/
theorem data_6_16 : oddCount 16 6 = 1 ∧
    acceleratedOrbit 6 16 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_16 : gap 6 16 = 61 ∧ 3 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_16 : threshold 6 16 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_16 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 16) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 16
  rw [data_6_16.1, data_6_16.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_16 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 16) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 16
  rw [data_6_16.1, data_6_16.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_16 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 16) < 64 * (2 * m) + 16 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 16 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_16] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 16) < 64 * (2 * m) + 16 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_16 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 16) < 64 * (2 * m + 1) + 16 := by
  apply refinement_cleared (k := 6) (r := 16) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_16]; decide

end Collatz.Research.RefinementAtlas.Batch022
