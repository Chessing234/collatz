import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 165. -/
namespace Collatz.Research.RefinementAtlas.Batch165
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 113). -/
theorem data_9_113 : oddCount 113 9 = 2 ∧
    acceleratedOrbit 9 113 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_113 : gap 9 113 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_113 : threshold 9 113 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_113 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 113) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 113
  rw [data_9_113.1, data_9_113.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_113 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 113) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 113
  rw [data_9_113.1, data_9_113.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_113 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 113) < 512 * (2 * m) + 113 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 113 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_113] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 113) < 512 * (2 * m) + 113 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_113 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 113) < 512 * (2 * m + 1) + 113 := by
  apply refinement_cleared (k := 9) (r := 113) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_113]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 114). -/
theorem data_9_114 : oddCount 114 9 = 5 ∧
    acceleratedOrbit 9 114 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_114 : gap 9 114 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_114 : threshold 9 114 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_114 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 114) = 243 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 114
  rw [data_9_114.1, data_9_114.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_114 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 114) = 243 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 114
  rw [data_9_114.1, data_9_114.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_114 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 114) < 512 * (2 * m) + 114 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 114 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_114] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 114) < 512 * (2 * m) + 114 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_114 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 114) < 512 * (2 * m + 1) + 114 := by
  apply refinement_cleared (k := 9) (r := 114) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_114]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 115). -/
theorem data_9_115 : oddCount 115 9 = 5 ∧
    acceleratedOrbit 9 115 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_115 : gap 9 115 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_115 : threshold 9 115 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_115 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 115) = 243 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 115
  rw [data_9_115.1, data_9_115.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_115 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 115) = 243 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 115
  rw [data_9_115.1, data_9_115.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_115 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 115) < 512 * (2 * m) + 115 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 115 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_115] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 115) < 512 * (2 * m) + 115 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_115 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 115) < 512 * (2 * m + 1) + 115 := by
  apply refinement_cleared (k := 9) (r := 115) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_115]; decide

end Collatz.Research.RefinementAtlas.Batch165
