import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 183. -/
namespace Collatz.Research.RefinementAtlas.Batch183
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 188). -/
theorem data_9_188 : oddCount 188 9 = 5 ∧
    acceleratedOrbit 9 188 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_188 : gap 9 188 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_188 : threshold 9 188 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_188 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 188) = 243 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 188
  rw [data_9_188.1, data_9_188.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_188 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 188) = 243 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 188
  rw [data_9_188.1, data_9_188.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_188 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 188) < 512 * (2 * m) + 188 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 188 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_188] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 188) < 512 * (2 * m) + 188 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_188 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 188) < 512 * (2 * m + 1) + 188 := by
  apply refinement_cleared (k := 9) (r := 188) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_188]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 189). -/
theorem data_9_189 : oddCount 189 9 = 5 ∧
    acceleratedOrbit 9 189 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_189 : gap 9 189 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_189 : threshold 9 189 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_189 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 189) = 243 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 189
  rw [data_9_189.1, data_9_189.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_189 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 189) = 243 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 189
  rw [data_9_189.1, data_9_189.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_189 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 189) < 512 * (2 * m) + 189 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 189 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_189] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 189) < 512 * (2 * m) + 189 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_189 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 189) < 512 * (2 * m + 1) + 189 := by
  apply refinement_cleared (k := 9) (r := 189) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_189]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 190). -/
theorem data_9_190 : oddCount 190 9 = 5 ∧
    acceleratedOrbit 9 190 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_190 : gap 9 190 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_190 : threshold 9 190 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_190 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 190) = 243 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 190
  rw [data_9_190.1, data_9_190.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_190 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 190) = 243 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 190
  rw [data_9_190.1, data_9_190.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_190 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 190) < 512 * (2 * m) + 190 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 190 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_190] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 190) < 512 * (2 * m) + 190 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_190 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 190) < 512 * (2 * m + 1) + 190 := by
  apply refinement_cleared (k := 9) (r := 190) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_190]; decide

end Collatz.Research.RefinementAtlas.Batch183
