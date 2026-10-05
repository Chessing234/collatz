import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 123. -/
namespace Collatz.Research.RefinementAtlas.Batch123
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 205). -/
theorem data_8_205 : oddCount 205 8 = 3 ∧
    acceleratedOrbit 8 205 = 22 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_205 : gap 8 205 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_205 : threshold 8 205 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_205 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 205) = 27 * (2 * m) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 205
  rw [data_8_205.1, data_8_205.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_205 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 205) = 27 * (2 * m + 1) + 22 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 205
  rw [data_8_205.1, data_8_205.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_205 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 205) < 256 * (2 * m) + 205 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 205 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_205] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 205) < 256 * (2 * m) + 205 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_205 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 205) < 256 * (2 * m + 1) + 205 := by
  apply refinement_cleared (k := 8) (r := 205) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_205]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 208). -/
theorem data_8_208 : oddCount 208 8 = 2 ∧
    acceleratedOrbit 8 208 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_208 : gap 8 208 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_208 : threshold 8 208 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_208 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 208) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 208
  rw [data_8_208.1, data_8_208.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_208 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 208) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 208
  rw [data_8_208.1, data_8_208.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_208 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 208) < 256 * (2 * m) + 208 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 208 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_208] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 208) < 256 * (2 * m) + 208 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_208 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 208) < 256 * (2 * m + 1) + 208 := by
  apply refinement_cleared (k := 8) (r := 208) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_208]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 209). -/
theorem data_8_209 : oddCount 209 8 = 4 ∧
    acceleratedOrbit 8 209 = 67 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_209 : gap 8 209 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_209 : threshold 8 209 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_209 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 209) = 81 * (2 * m) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 209
  rw [data_8_209.1, data_8_209.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_209 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 209) = 81 * (2 * m + 1) + 67 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 209
  rw [data_8_209.1, data_8_209.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_209 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 209) < 256 * (2 * m) + 209 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 209 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_209] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 209) < 256 * (2 * m) + 209 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_209 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 209) < 256 * (2 * m + 1) + 209 := by
  apply refinement_cleared (k := 8) (r := 209) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_209]; decide

end Collatz.Research.RefinementAtlas.Batch123
