import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 285. -/
namespace Collatz.Research.RefinementAtlas.Batch285
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 84). -/
theorem data_10_84 : oddCount 84 10 = 2 ∧
    acceleratedOrbit 10 84 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_84 : gap 10 84 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_84 : threshold 10 84 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_84 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 84) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 84
  rw [data_10_84.1, data_10_84.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_84 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 84) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 84
  rw [data_10_84.1, data_10_84.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_84 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 84) < 1024 * (2 * m) + 84 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 84 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_84] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 84) < 1024 * (2 * m) + 84 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_84 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 84) < 1024 * (2 * m + 1) + 84 := by
  apply refinement_cleared (k := 10) (r := 84) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_84]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 85). -/
theorem data_10_85 : oddCount 85 10 = 2 ∧
    acceleratedOrbit 10 85 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_85 : gap 10 85 = 1015 ∧ 9 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_85 : threshold 10 85 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_85 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 85) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 85
  rw [data_10_85.1, data_10_85.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_85 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 85) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 85
  rw [data_10_85.1, data_10_85.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_85 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 85) < 1024 * (2 * m) + 85 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 85 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_85] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 85) < 1024 * (2 * m) + 85 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_85 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 85) < 1024 * (2 * m + 1) + 85 := by
  apply refinement_cleared (k := 10) (r := 85) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_85]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 86). -/
theorem data_10_86 : oddCount 86 10 = 4 ∧
    acceleratedOrbit 10 86 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_86 : gap 10 86 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_86 : threshold 10 86 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_86 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 86) = 81 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 86
  rw [data_10_86.1, data_10_86.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_86 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 86) = 81 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 86
  rw [data_10_86.1, data_10_86.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_86 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 86) < 1024 * (2 * m) + 86 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 86 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_86] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 86) < 1024 * (2 * m) + 86 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_86 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 86) < 1024 * (2 * m + 1) + 86 := by
  apply refinement_cleared (k := 10) (r := 86) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_86]; decide

end Collatz.Research.RefinementAtlas.Batch285
