import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 126. -/
namespace Collatz.Research.RefinementAtlas.Batch126
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 216). -/
theorem data_8_216 : oddCount 216 8 = 4 ∧
    acceleratedOrbit 8 216 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_216 : gap 8 216 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_216 : threshold 8 216 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_216 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 216) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 216
  rw [data_8_216.1, data_8_216.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_216 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 216) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 216
  rw [data_8_216.1, data_8_216.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_216 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 216) < 256 * (2 * m) + 216 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 216 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_216] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 216) < 256 * (2 * m) + 216 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_216 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 216) < 256 * (2 * m + 1) + 216 := by
  apply refinement_cleared (k := 8) (r := 216) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_216]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 217). -/
theorem data_8_217 : oddCount 217 8 = 3 ∧
    acceleratedOrbit 8 217 = 23 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_217 : gap 8 217 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_217 : threshold 8 217 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_217 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 217) = 27 * (2 * m) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 217
  rw [data_8_217.1, data_8_217.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_217 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 217) = 27 * (2 * m + 1) + 23 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 217
  rw [data_8_217.1, data_8_217.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_217 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 217) < 256 * (2 * m) + 217 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 217 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_217] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 217) < 256 * (2 * m) + 217 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_217 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 217) < 256 * (2 * m + 1) + 217 := by
  apply refinement_cleared (k := 8) (r := 217) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_217]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 218). -/
theorem data_8_218 : oddCount 218 8 = 4 ∧
    acceleratedOrbit 8 218 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_218 : gap 8 218 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_218 : threshold 8 218 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_218 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 218) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 218
  rw [data_8_218.1, data_8_218.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_218 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 218) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 218
  rw [data_8_218.1, data_8_218.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_218 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 218) < 256 * (2 * m) + 218 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 218 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_218] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 218) < 256 * (2 * m) + 218 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_218 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 218) < 256 * (2 * m + 1) + 218 := by
  apply refinement_cleared (k := 8) (r := 218) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_218]; decide

end Collatz.Research.RefinementAtlas.Batch126
