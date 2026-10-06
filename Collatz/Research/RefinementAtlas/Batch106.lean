import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 106. -/
namespace Collatz.Research.RefinementAtlas.Batch106
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 149). -/
theorem data_8_149 : oddCount 149 8 = 3 ∧
    acceleratedOrbit 8 149 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_149 : gap 8 149 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_149 : threshold 8 149 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_149 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 149) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 149
  rw [data_8_149.1, data_8_149.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_149 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 149) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 149
  rw [data_8_149.1, data_8_149.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_149 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 149) < 256 * (2 * m) + 149 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 149 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_149] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 149) < 256 * (2 * m) + 149 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_149 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 149) < 256 * (2 * m + 1) + 149 := by
  apply refinement_cleared (k := 8) (r := 149) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_149]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 150). -/
theorem data_8_150 : oddCount 150 8 = 3 ∧
    acceleratedOrbit 8 150 = 16 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_150 : gap 8 150 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_150 : threshold 8 150 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_150 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 150) = 27 * (2 * m) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 150
  rw [data_8_150.1, data_8_150.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_150 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 150) = 27 * (2 * m + 1) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 150
  rw [data_8_150.1, data_8_150.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_150 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 150) < 256 * (2 * m) + 150 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 150 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_150] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 150) < 256 * (2 * m) + 150 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_150 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 150) < 256 * (2 * m + 1) + 150 := by
  apply refinement_cleared (k := 8) (r := 150) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_150]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 151). -/
theorem data_8_151 : oddCount 151 8 = 3 ∧
    acceleratedOrbit 8 151 = 16 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_151 : gap 8 151 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_151 : threshold 8 151 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_151 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 151) = 27 * (2 * m) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 151
  rw [data_8_151.1, data_8_151.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_151 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 151) = 27 * (2 * m + 1) + 16 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 151
  rw [data_8_151.1, data_8_151.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_151 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 151) < 256 * (2 * m) + 151 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 151 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_151] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 151) < 256 * (2 * m) + 151 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_151 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 151) < 256 * (2 * m + 1) + 151 := by
  apply refinement_cleared (k := 8) (r := 151) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_151]; decide

end Collatz.Research.RefinementAtlas.Batch106
