import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 127. -/
namespace Collatz.Research.RefinementAtlas.Batch127
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 219). -/
theorem data_8_219 : oddCount 219 8 = 5 ∧
    acceleratedOrbit 8 219 = 209 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_219 : gap 8 219 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_219 : threshold 8 219 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_219 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 219) = 243 * (2 * m) + 209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 219
  rw [data_8_219.1, data_8_219.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_219 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 219) = 243 * (2 * m + 1) + 209 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 219
  rw [data_8_219.1, data_8_219.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_219 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 219) < 256 * (2 * m) + 219 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 219 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_219] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 219) < 256 * (2 * m) + 219 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_219 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 219) < 256 * (2 * m + 1) + 219 := by
  apply refinement_cleared (k := 8) (r := 219) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_219]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 220). -/
theorem data_8_220 : oddCount 220 8 = 4 ∧
    acceleratedOrbit 8 220 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_220 : gap 8 220 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_220 : threshold 8 220 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_220 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 220) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 220
  rw [data_8_220.1, data_8_220.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_220 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 220) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 220
  rw [data_8_220.1, data_8_220.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_220 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 220) < 256 * (2 * m) + 220 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 220 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_220] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 220) < 256 * (2 * m) + 220 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_220 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 220) < 256 * (2 * m + 1) + 220 := by
  apply refinement_cleared (k := 8) (r := 220) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_220]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 221). -/
theorem data_8_221 : oddCount 221 8 = 4 ∧
    acceleratedOrbit 8 221 = 71 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_221 : gap 8 221 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_221 : threshold 8 221 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_221 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 221) = 81 * (2 * m) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 221
  rw [data_8_221.1, data_8_221.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_221 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 221) = 81 * (2 * m + 1) + 71 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 221
  rw [data_8_221.1, data_8_221.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_221 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 221) < 256 * (2 * m) + 221 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 221 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_221] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 221) < 256 * (2 * m) + 221 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_221 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 221) < 256 * (2 * m + 1) + 221 := by
  apply refinement_cleared (k := 8) (r := 221) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_221]; decide

end Collatz.Research.RefinementAtlas.Batch127
