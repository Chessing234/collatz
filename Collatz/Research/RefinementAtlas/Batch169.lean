import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 169. -/
namespace Collatz.Research.RefinementAtlas.Batch169
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 131). -/
theorem data_9_131 : oddCount 131 9 = 3 ∧
    acceleratedOrbit 9 131 = 7 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_131 : gap 9 131 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_131 : threshold 9 131 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_131 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 131) = 27 * (2 * m) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 131
  rw [data_9_131.1, data_9_131.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_131 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 131) = 27 * (2 * m + 1) + 7 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 131
  rw [data_9_131.1, data_9_131.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_131 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 131) < 512 * (2 * m) + 131 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 131 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_131] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 131) < 512 * (2 * m) + 131 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_131 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 131) < 512 * (2 * m + 1) + 131 := by
  apply refinement_cleared (k := 9) (r := 131) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_131]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 132). -/
theorem data_9_132 : oddCount 132 9 = 4 ∧
    acceleratedOrbit 9 132 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_132 : gap 9 132 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_132 : threshold 9 132 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_132 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 132) = 81 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 132
  rw [data_9_132.1, data_9_132.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_132 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 132) = 81 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 132
  rw [data_9_132.1, data_9_132.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_132 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 132) < 512 * (2 * m) + 132 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 132 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_132] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 132) < 512 * (2 * m) + 132 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_132 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 132) < 512 * (2 * m + 1) + 132 := by
  apply refinement_cleared (k := 9) (r := 132) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_132]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 133). -/
theorem data_9_133 : oddCount 133 9 = 4 ∧
    acceleratedOrbit 9 133 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_133 : gap 9 133 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_133 : threshold 9 133 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_133 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 133) = 81 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 133
  rw [data_9_133.1, data_9_133.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_133 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 133) = 81 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 133
  rw [data_9_133.1, data_9_133.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_133 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 133) < 512 * (2 * m) + 133 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 133 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_133] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 133) < 512 * (2 * m) + 133 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_133 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 133) < 512 * (2 * m + 1) + 133 := by
  apply refinement_cleared (k := 9) (r := 133) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_133]; decide

end Collatz.Research.RefinementAtlas.Batch169
