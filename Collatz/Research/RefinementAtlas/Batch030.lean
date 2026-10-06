import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 030. -/
namespace Collatz.Research.RefinementAtlas.Batch030
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 48). -/
theorem data_6_48 : oddCount 48 6 = 2 ∧
    acceleratedOrbit 6 48 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_48 : gap 6 48 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_48 : threshold 6 48 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_48 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 48) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 48
  rw [data_6_48.1, data_6_48.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_48 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 48) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 48
  rw [data_6_48.1, data_6_48.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_48 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 48) < 64 * (2 * m) + 48 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 48 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_48] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 48) < 64 * (2 * m) + 48 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_48 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 48) < 64 * (2 * m + 1) + 48 := by
  apply refinement_cleared (k := 6) (r := 48) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_48]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 49). -/
theorem data_6_49 : oddCount 49 6 = 2 ∧
    acceleratedOrbit 6 49 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_49 : gap 6 49 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_49 : threshold 6 49 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_49 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 49) = 9 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 49
  rw [data_6_49.1, data_6_49.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_49 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 49) = 9 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 49
  rw [data_6_49.1, data_6_49.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_49 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 49) < 64 * (2 * m) + 49 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 49 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_49] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 49) < 64 * (2 * m) + 49 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_49 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 49) < 64 * (2 * m + 1) + 49 := by
  apply refinement_cleared (k := 6) (r := 49) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_49]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 50). -/
theorem data_6_50 : oddCount 50 6 = 3 ∧
    acceleratedOrbit 6 50 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_50 : gap 6 50 = 37 ∧ 27 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_50 : threshold 6 50 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_50 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 50) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 50
  rw [data_6_50.1, data_6_50.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_50 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 50) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 50
  rw [data_6_50.1, data_6_50.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_50 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 50) < 64 * (2 * m) + 50 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 50 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_50] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 50) < 64 * (2 * m) + 50 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_50 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 50) < 64 * (2 * m + 1) + 50 := by
  apply refinement_cleared (k := 6) (r := 50) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_50]; decide

end Collatz.Research.RefinementAtlas.Batch030
