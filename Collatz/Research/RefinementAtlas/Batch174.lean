import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 174. -/
namespace Collatz.Research.RefinementAtlas.Batch174
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 149). -/
theorem data_9_149 : oddCount 149 9 = 4 ∧
    acceleratedOrbit 9 149 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_149 : gap 9 149 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_149 : threshold 9 149 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_149 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 149) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 149
  rw [data_9_149.1, data_9_149.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_149 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 149) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 149
  rw [data_9_149.1, data_9_149.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_149 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 149) < 512 * (2 * m) + 149 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 149 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_149] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 149) < 512 * (2 * m) + 149 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_149 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 149) < 512 * (2 * m + 1) + 149 := by
  apply refinement_cleared (k := 9) (r := 149) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_149]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 150). -/
theorem data_9_150 : oddCount 150 9 = 3 ∧
    acceleratedOrbit 9 150 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_150 : gap 9 150 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_150 : threshold 9 150 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_150 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 150) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 150
  rw [data_9_150.1, data_9_150.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_150 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 150) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 150
  rw [data_9_150.1, data_9_150.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_150 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 150) < 512 * (2 * m) + 150 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 150 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_150] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 150) < 512 * (2 * m) + 150 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_150 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 150) < 512 * (2 * m + 1) + 150 := by
  apply refinement_cleared (k := 9) (r := 150) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_150]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 151). -/
theorem data_9_151 : oddCount 151 9 = 3 ∧
    acceleratedOrbit 9 151 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_151 : gap 9 151 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_151 : threshold 9 151 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_151 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 151) = 27 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 151
  rw [data_9_151.1, data_9_151.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_151 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 151) = 27 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 151
  rw [data_9_151.1, data_9_151.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_151 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 151) < 512 * (2 * m) + 151 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 151 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_151] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 151) < 512 * (2 * m) + 151 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_151 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 151) < 512 * (2 * m + 1) + 151 := by
  apply refinement_cleared (k := 9) (r := 151) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_151]; decide

end Collatz.Research.RefinementAtlas.Batch174
