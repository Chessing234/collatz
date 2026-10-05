import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 288. -/
namespace Collatz.Research.RefinementAtlas.Batch288
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 96). -/
theorem data_10_96 : oddCount 96 10 = 2 ∧
    acceleratedOrbit 10 96 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_96 : gap 10 96 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_96 : threshold 10 96 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_96 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 96) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 96
  rw [data_10_96.1, data_10_96.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_96 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 96) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 96
  rw [data_10_96.1, data_10_96.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_96 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 96) < 1024 * (2 * m) + 96 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 96 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_96] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 96) < 1024 * (2 * m) + 96 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_96 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 96) < 1024 * (2 * m + 1) + 96 := by
  apply refinement_cleared (k := 10) (r := 96) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_96]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 97). -/
theorem data_10_97 : oddCount 97 10 = 6 ∧
    acceleratedOrbit 10 97 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_97 : gap 10 97 = 295 ∧ 729 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_97 : threshold 10 97 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_97 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 97) = 729 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 97
  rw [data_10_97.1, data_10_97.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_97 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 97) = 729 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 97
  rw [data_10_97.1, data_10_97.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_97 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 97) < 1024 * (2 * m) + 97 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 97 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_97] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 97) < 1024 * (2 * m) + 97 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_97 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 97) < 1024 * (2 * m + 1) + 97 := by
  apply refinement_cleared (k := 10) (r := 97) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_97]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 98). -/
theorem data_10_98 : oddCount 98 10 = 5 ∧
    acceleratedOrbit 10 98 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_98 : gap 10 98 = 781 ∧ 243 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_98 : threshold 10 98 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_98 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 98) = 243 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 98
  rw [data_10_98.1, data_10_98.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_98 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 98) = 243 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 98
  rw [data_10_98.1, data_10_98.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_98 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 98) < 1024 * (2 * m) + 98 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 98 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_98] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 98) < 1024 * (2 * m) + 98 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_98 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 98) < 1024 * (2 * m + 1) + 98 := by
  apply refinement_cleared (k := 10) (r := 98) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_98]; decide

end Collatz.Research.RefinementAtlas.Batch288
