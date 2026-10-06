import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 193. -/
namespace Collatz.Research.RefinementAtlas.Batch193
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 224). -/
theorem data_9_224 : oddCount 224 9 = 3 ∧
    acceleratedOrbit 9 224 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_224 : gap 9 224 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_224 : threshold 9 224 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_224 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 224) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 224
  rw [data_9_224.1, data_9_224.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_224 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 224) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 224
  rw [data_9_224.1, data_9_224.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_224 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 224) < 512 * (2 * m) + 224 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 224 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_224] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 224) < 512 * (2 * m) + 224 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_224 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 224) < 512 * (2 * m + 1) + 224 := by
  apply refinement_cleared (k := 9) (r := 224) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_224]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 226). -/
theorem data_9_226 : oddCount 226 9 = 2 ∧
    acceleratedOrbit 9 226 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_226 : gap 9 226 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_226 : threshold 9 226 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_226 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 226) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 226
  rw [data_9_226.1, data_9_226.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_226 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 226) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 226
  rw [data_9_226.1, data_9_226.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_226 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 226) < 512 * (2 * m) + 226 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 226 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_226] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 226) < 512 * (2 * m) + 226 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_226 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 226) < 512 * (2 * m + 1) + 226 := by
  apply refinement_cleared (k := 9) (r := 226) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_226]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 227). -/
theorem data_9_227 : oddCount 227 9 = 2 ∧
    acceleratedOrbit 9 227 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_227 : gap 9 227 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_227 : threshold 9 227 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_227 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 227) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 227
  rw [data_9_227.1, data_9_227.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_227 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 227) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 227
  rw [data_9_227.1, data_9_227.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_227 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 227) < 512 * (2 * m) + 227 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 227 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_227] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 227) < 512 * (2 * m) + 227 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_227 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 227) < 512 * (2 * m + 1) + 227 := by
  apply refinement_cleared (k := 9) (r := 227) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_227]; decide

end Collatz.Research.RefinementAtlas.Batch193
