import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 113. -/
namespace Collatz.Research.RefinementAtlas.Batch113
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 174). -/
theorem data_8_174 : oddCount 174 8 = 4 ∧
    acceleratedOrbit 8 174 = 56 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_174 : gap 8 174 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_174 : threshold 8 174 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_174 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 174) = 81 * (2 * m) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 174
  rw [data_8_174.1, data_8_174.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_174 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 174) = 81 * (2 * m + 1) + 56 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 174
  rw [data_8_174.1, data_8_174.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_174 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 174) < 256 * (2 * m) + 174 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 174 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_174] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 174) < 256 * (2 * m) + 174 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_174 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 174) < 256 * (2 * m + 1) + 174 := by
  apply refinement_cleared (k := 8) (r := 174) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_174]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 175). -/
theorem data_8_175 : oddCount 175 8 = 5 ∧
    acceleratedOrbit 8 175 = 167 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_175 : gap 8 175 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_175 : threshold 8 175 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_175 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 175) = 243 * (2 * m) + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 175
  rw [data_8_175.1, data_8_175.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_175 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 175) = 243 * (2 * m + 1) + 167 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 175
  rw [data_8_175.1, data_8_175.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_175 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 175) < 256 * (2 * m) + 175 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 175 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_175] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 175) < 256 * (2 * m) + 175 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_175 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 175) < 256 * (2 * m + 1) + 175 := by
  apply refinement_cleared (k := 8) (r := 175) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_175]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 176). -/
theorem data_8_176 : oddCount 176 8 = 3 ∧
    acceleratedOrbit 8 176 = 20 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_176 : gap 8 176 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_176 : threshold 8 176 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_176 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 176) = 27 * (2 * m) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 176
  rw [data_8_176.1, data_8_176.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_176 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 176) = 27 * (2 * m + 1) + 20 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 176
  rw [data_8_176.1, data_8_176.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_176 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 176) < 256 * (2 * m) + 176 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 176 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_176] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 176) < 256 * (2 * m) + 176 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_176 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 176) < 256 * (2 * m + 1) + 176 := by
  apply refinement_cleared (k := 8) (r := 176) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_176]; decide

end Collatz.Research.RefinementAtlas.Batch113
