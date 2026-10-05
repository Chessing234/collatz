import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 128. -/
namespace Collatz.Research.RefinementAtlas.Batch128
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 224). -/
theorem data_8_224 : oddCount 224 8 = 3 ∧
    acceleratedOrbit 8 224 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_224 : gap 8 224 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_224 : threshold 8 224 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_224 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 224) = 27 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 224
  rw [data_8_224.1, data_8_224.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_224 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 224) = 27 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 224
  rw [data_8_224.1, data_8_224.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_224 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 224) < 256 * (2 * m) + 224 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 224 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_224] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 224) < 256 * (2 * m) + 224 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_224 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 224) < 256 * (2 * m + 1) + 224 := by
  apply refinement_cleared (k := 8) (r := 224) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_224]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 226). -/
theorem data_8_226 : oddCount 226 8 = 2 ∧
    acceleratedOrbit 8 226 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_226 : gap 8 226 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_226 : threshold 8 226 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_226 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 226) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 226
  rw [data_8_226.1, data_8_226.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_226 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 226) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 226
  rw [data_8_226.1, data_8_226.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_226 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 226) < 256 * (2 * m) + 226 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 226 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_226] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 226) < 256 * (2 * m) + 226 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_226 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 226) < 256 * (2 * m + 1) + 226 := by
  apply refinement_cleared (k := 8) (r := 226) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_226]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 227). -/
theorem data_8_227 : oddCount 227 8 = 2 ∧
    acceleratedOrbit 8 227 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_227 : gap 8 227 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_227 : threshold 8 227 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_227 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 227) = 9 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 227
  rw [data_8_227.1, data_8_227.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_227 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 227) = 9 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 227
  rw [data_8_227.1, data_8_227.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_227 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 227) < 256 * (2 * m) + 227 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 227 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_227] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 227) < 256 * (2 * m) + 227 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_227 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 227) < 256 * (2 * m + 1) + 227 := by
  apply refinement_cleared (k := 8) (r := 227) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_227]; decide

end Collatz.Research.RefinementAtlas.Batch128
