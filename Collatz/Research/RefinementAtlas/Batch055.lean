import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 055. -/
namespace Collatz.Research.RefinementAtlas.Batch055
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 84). -/
theorem data_7_84 : oddCount 84 7 = 1 ∧
    acceleratedOrbit 7 84 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_84 : gap 7 84 = 125 ∧ 3 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_84 : threshold 7 84 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_84 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 84) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 84
  rw [data_7_84.1, data_7_84.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_84 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 84) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 84
  rw [data_7_84.1, data_7_84.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_84 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 84) < 128 * (2 * m) + 84 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 84 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_84] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 84) < 128 * (2 * m) + 84 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_84 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 84) < 128 * (2 * m + 1) + 84 := by
  apply refinement_cleared (k := 7) (r := 84) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_84]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 85). -/
theorem data_7_85 : oddCount 85 7 = 1 ∧
    acceleratedOrbit 7 85 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_85 : gap 7 85 = 125 ∧ 3 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_85 : threshold 7 85 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_85 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 85) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 85
  rw [data_7_85.1, data_7_85.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_85 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 85) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 85
  rw [data_7_85.1, data_7_85.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_85 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 85) < 128 * (2 * m) + 85 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 85 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_85] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 85) < 128 * (2 * m) + 85 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_85 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 85) < 128 * (2 * m + 1) + 85 := by
  apply refinement_cleared (k := 7) (r := 85) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_85]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 86). -/
theorem data_7_86 : oddCount 86 7 = 4 ∧
    acceleratedOrbit 7 86 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_86 : gap 7 86 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_86 : threshold 7 86 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_86 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 86) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 86
  rw [data_7_86.1, data_7_86.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_86 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 86) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 86
  rw [data_7_86.1, data_7_86.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_86 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 86) < 128 * (2 * m) + 86 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 86 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_86] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 86) < 128 * (2 * m) + 86 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_86 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 86) < 128 * (2 * m + 1) + 86 := by
  apply refinement_cleared (k := 7) (r := 86) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_86]; decide

end Collatz.Research.RefinementAtlas.Batch055
