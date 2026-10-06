import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 111. -/
namespace Collatz.Research.RefinementAtlas.Batch111
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 166). -/
theorem data_8_166 : oddCount 166 8 = 5 ∧
    acceleratedOrbit 8 166 = 161 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_166 : gap 8 166 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_166 : threshold 8 166 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_166 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 166) = 243 * (2 * m) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 166
  rw [data_8_166.1, data_8_166.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_166 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 166) = 243 * (2 * m + 1) + 161 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 166
  rw [data_8_166.1, data_8_166.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_166 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 166) < 256 * (2 * m) + 166 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 166 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_166] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 166) < 256 * (2 * m) + 166 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_166 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 166) < 256 * (2 * m + 1) + 166 := by
  apply refinement_cleared (k := 8) (r := 166) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_166]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 168). -/
theorem data_8_168 : oddCount 168 8 = 1 ∧
    acceleratedOrbit 8 168 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_168 : gap 8 168 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_168 : threshold 8 168 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_168 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 168) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 168
  rw [data_8_168.1, data_8_168.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_168 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 168) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 168
  rw [data_8_168.1, data_8_168.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_168 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 168) < 256 * (2 * m) + 168 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 168 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_168] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 168) < 256 * (2 * m) + 168 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_168 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 168) < 256 * (2 * m + 1) + 168 := by
  apply refinement_cleared (k := 8) (r := 168) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_168]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 170). -/
theorem data_8_170 : oddCount 170 8 = 1 ∧
    acceleratedOrbit 8 170 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_170 : gap 8 170 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_170 : threshold 8 170 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_170 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 170) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 170
  rw [data_8_170.1, data_8_170.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_170 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 170) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 170
  rw [data_8_170.1, data_8_170.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_170 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 170) < 256 * (2 * m) + 170 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 170 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_170] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 170) < 256 * (2 * m) + 170 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_170 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 170) < 256 * (2 * m + 1) + 170 := by
  apply refinement_cleared (k := 8) (r := 170) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_170]; decide

end Collatz.Research.RefinementAtlas.Batch111
