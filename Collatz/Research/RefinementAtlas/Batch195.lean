import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 195. -/
namespace Collatz.Research.RefinementAtlas.Batch195
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 232). -/
theorem data_9_232 : oddCount 232 9 = 3 ∧
    acceleratedOrbit 9 232 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_232 : gap 9 232 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_232 : threshold 9 232 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_232 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 232) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 232
  rw [data_9_232.1, data_9_232.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_232 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 232) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 232
  rw [data_9_232.1, data_9_232.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_232 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 232) < 512 * (2 * m) + 232 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 232 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_232] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 232) < 512 * (2 * m) + 232 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_232 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 232) < 512 * (2 * m + 1) + 232 := by
  apply refinement_cleared (k := 9) (r := 232) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_232]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 234). -/
theorem data_9_234 : oddCount 234 9 = 3 ∧
    acceleratedOrbit 9 234 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_234 : gap 9 234 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_234 : threshold 9 234 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_234 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 234) = 27 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 234
  rw [data_9_234.1, data_9_234.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_234 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 234) = 27 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 234
  rw [data_9_234.1, data_9_234.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_234 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 234) < 512 * (2 * m) + 234 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 234 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_234] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 234) < 512 * (2 * m) + 234 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_234 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 234) < 512 * (2 * m + 1) + 234 := by
  apply refinement_cleared (k := 9) (r := 234) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_234]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 236). -/
theorem data_9_236 : oddCount 236 9 = 4 ∧
    acceleratedOrbit 9 236 = 38 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_236 : gap 9 236 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_236 : threshold 9 236 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_236 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 236) = 81 * (2 * m) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 236
  rw [data_9_236.1, data_9_236.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_236 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 236) = 81 * (2 * m + 1) + 38 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 236
  rw [data_9_236.1, data_9_236.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_236 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 236) < 512 * (2 * m) + 236 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 236 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_236] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 236) < 512 * (2 * m) + 236 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_236 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 236) < 512 * (2 * m + 1) + 236 := by
  apply refinement_cleared (k := 9) (r := 236) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_236]; decide

end Collatz.Research.RefinementAtlas.Batch195
