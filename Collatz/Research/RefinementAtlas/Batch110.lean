import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 110. -/
namespace Collatz.Research.RefinementAtlas.Batch110
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 163). -/
theorem data_8_163 : oddCount 163 8 = 4 ∧
    acceleratedOrbit 8 163 = 53 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_163 : gap 8 163 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_163 : threshold 8 163 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_163 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 163) = 81 * (2 * m) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 163
  rw [data_8_163.1, data_8_163.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_163 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 163) = 81 * (2 * m + 1) + 53 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 163
  rw [data_8_163.1, data_8_163.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_163 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 163) < 256 * (2 * m) + 163 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 163 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_163] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 163) < 256 * (2 * m) + 163 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_163 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 163) < 256 * (2 * m + 1) + 163 := by
  apply refinement_cleared (k := 8) (r := 163) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_163]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 164). -/
theorem data_8_164 : oddCount 164 8 = 5 ∧
    acceleratedOrbit 8 164 = 161 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_164 : gap 8 164 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_164 : threshold 8 164 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_164 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 164) = 243 * (2 * m) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 164
  rw [data_8_164.1, data_8_164.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_164 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 164) = 243 * (2 * m + 1) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 164
  rw [data_8_164.1, data_8_164.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_164 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 164) < 256 * (2 * m) + 164 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 164 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_164] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 164) < 256 * (2 * m) + 164 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_164 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 164) < 256 * (2 * m + 1) + 164 := by
  apply refinement_cleared (k := 8) (r := 164) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_164]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 165). -/
theorem data_8_165 : oddCount 165 8 = 5 ∧
    acceleratedOrbit 8 165 = 161 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_165 : gap 8 165 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_165 : threshold 8 165 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_165 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 165) = 243 * (2 * m) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 165
  rw [data_8_165.1, data_8_165.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_165 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 165) = 243 * (2 * m + 1) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 165
  rw [data_8_165.1, data_8_165.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_165 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 165) < 256 * (2 * m) + 165 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 165 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_165] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 165) < 256 * (2 * m) + 165 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_165 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 165) < 256 * (2 * m + 1) + 165 := by
  apply refinement_cleared (k := 8) (r := 165) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_165]; decide

end Collatz.Research.RefinementAtlas.Batch110
