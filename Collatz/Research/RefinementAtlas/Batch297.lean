import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 297. -/
namespace Collatz.Research.RefinementAtlas.Batch297
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (10, 131). -/
theorem data_10_131 : oddCount 131 10 = 4 ∧
    acceleratedOrbit 10 131 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_131 : gap 10 131 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_131 : threshold 10 131 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_131 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 131) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 131
  rw [data_10_131.1, data_10_131.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_131 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 131) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 131
  rw [data_10_131.1, data_10_131.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_131 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 131) < 1024 * (2 * m) + 131 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 131 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_131] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 131) < 1024 * (2 * m) + 131 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_131 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 131) < 1024 * (2 * m + 1) + 131 := by
  apply refinement_cleared (k := 10) (r := 131) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_131]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 132). -/
theorem data_10_132 : oddCount 132 10 = 4 ∧
    acceleratedOrbit 10 132 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_132 : gap 10 132 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_132 : threshold 10 132 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_132 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 132) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 132
  rw [data_10_132.1, data_10_132.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_132 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 132) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 132
  rw [data_10_132.1, data_10_132.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_132 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 132) < 1024 * (2 * m) + 132 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 132 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_132] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 132) < 1024 * (2 * m) + 132 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_132 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 132) < 1024 * (2 * m + 1) + 132 := by
  apply refinement_cleared (k := 10) (r := 132) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_132]; decide

/-- Kernel-evaluated parity count and endpoint for (10, 133). -/
theorem data_10_133 : oddCount 133 10 = 4 ∧
    acceleratedOrbit 10 133 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_10_133 : gap 10 133 = 943 ∧ 81 < 1024 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_10_133 : threshold 10 133 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_10_133 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 133) = 81 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m) 133
  rw [data_10_133.1, data_10_133.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_10_133 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 133) = 81 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 10 (2 * m + 1) 133
  rw [data_10_133.1, data_10_133.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_10_133 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m) + 133) < 1024 * (2 * m) + 133 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 133 10 < 2 ^ 10 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_10_133] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 10 (1024 * (2 * m) + 133) < 1024 * (2 * m) + 133 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_10_133 (m : Nat) :
    acceleratedOrbit 10 (1024 * (2 * m + 1) + 133) < 1024 * (2 * m + 1) + 133 := by
  apply refinement_cleared (k := 10) (r := 133) (s := 2) (q := 1)
  · decide
  · rw [cutoff_10_133]; decide

end Collatz.Research.RefinementAtlas.Batch297
