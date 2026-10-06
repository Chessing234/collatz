import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 185. -/
namespace Collatz.Research.RefinementAtlas.Batch185
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 195). -/
theorem data_9_195 : oddCount 195 9 = 5 ∧
    acceleratedOrbit 9 195 = 94 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_195 : gap 9 195 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_195 : threshold 9 195 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_195 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 195) = 243 * (2 * m) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 195
  rw [data_9_195.1, data_9_195.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_195 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 195) = 243 * (2 * m + 1) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 195
  rw [data_9_195.1, data_9_195.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_195 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 195) < 512 * (2 * m) + 195 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 195 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_195] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 195) < 512 * (2 * m) + 195 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_195 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 195) < 512 * (2 * m + 1) + 195 := by
  apply refinement_cleared (k := 9) (r := 195) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_195]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 196). -/
theorem data_9_196 : oddCount 196 9 = 3 ∧
    acceleratedOrbit 9 196 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_196 : gap 9 196 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_196 : threshold 9 196 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_196 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 196) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 196
  rw [data_9_196.1, data_9_196.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_196 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 196) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 196
  rw [data_9_196.1, data_9_196.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_196 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 196) < 512 * (2 * m) + 196 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 196 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_196] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 196) < 512 * (2 * m) + 196 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_196 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 196) < 512 * (2 * m + 1) + 196 := by
  apply refinement_cleared (k := 9) (r := 196) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_196]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 197). -/
theorem data_9_197 : oddCount 197 9 = 3 ∧
    acceleratedOrbit 9 197 = 11 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_197 : gap 9 197 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_197 : threshold 9 197 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_197 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 197) = 27 * (2 * m) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 197
  rw [data_9_197.1, data_9_197.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_197 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 197) = 27 * (2 * m + 1) + 11 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 197
  rw [data_9_197.1, data_9_197.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_197 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 197) < 512 * (2 * m) + 197 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 197 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_197] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 197) < 512 * (2 * m) + 197 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_197 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 197) < 512 * (2 * m + 1) + 197 := by
  apply refinement_cleared (k := 9) (r := 197) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_197]; decide

end Collatz.Research.RefinementAtlas.Batch185
