import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 184. -/
namespace Collatz.Research.RefinementAtlas.Batch184
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 192). -/
theorem data_9_192 : oddCount 192 9 = 2 ∧
    acceleratedOrbit 9 192 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_192 : gap 9 192 = 503 ∧ 9 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_192 : threshold 9 192 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_192 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 192) = 9 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 192
  rw [data_9_192.1, data_9_192.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_192 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 192) = 9 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 192
  rw [data_9_192.1, data_9_192.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_192 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 192) < 512 * (2 * m) + 192 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 192 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_192] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 192) < 512 * (2 * m) + 192 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_192 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 192) < 512 * (2 * m + 1) + 192 := by
  apply refinement_cleared (k := 9) (r := 192) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_192]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 193). -/
theorem data_9_193 : oddCount 193 9 = 4 ∧
    acceleratedOrbit 9 193 = 31 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_193 : gap 9 193 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_193 : threshold 9 193 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_193 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 193) = 81 * (2 * m) + 31 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 193
  rw [data_9_193.1, data_9_193.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_193 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 193) = 81 * (2 * m + 1) + 31 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 193
  rw [data_9_193.1, data_9_193.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_193 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 193) < 512 * (2 * m) + 193 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 193 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_193] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 193) < 512 * (2 * m) + 193 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_193 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 193) < 512 * (2 * m + 1) + 193 := by
  apply refinement_cleared (k := 9) (r := 193) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_193]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 194). -/
theorem data_9_194 : oddCount 194 9 = 5 ∧
    acceleratedOrbit 9 194 = 94 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_194 : gap 9 194 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_194 : threshold 9 194 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_194 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 194) = 243 * (2 * m) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 194
  rw [data_9_194.1, data_9_194.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_194 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 194) = 243 * (2 * m + 1) + 94 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 194
  rw [data_9_194.1, data_9_194.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_194 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 194) < 512 * (2 * m) + 194 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 194 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_194] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 194) < 512 * (2 * m) + 194 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_194 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 194) < 512 * (2 * m + 1) + 194 := by
  apply refinement_cleared (k := 9) (r := 194) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_194]; decide

end Collatz.Research.RefinementAtlas.Batch184
