import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 198. -/
namespace Collatz.Research.RefinementAtlas.Batch198
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 246). -/
theorem data_9_246 : oddCount 246 9 = 5 ∧
    acceleratedOrbit 9 246 = 118 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_246 : gap 9 246 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_246 : threshold 9 246 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_246 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 246) = 243 * (2 * m) + 118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 246
  rw [data_9_246.1, data_9_246.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_246 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 246) = 243 * (2 * m + 1) + 118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 246
  rw [data_9_246.1, data_9_246.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_246 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 246) < 512 * (2 * m) + 246 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 246 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_246] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 246) < 512 * (2 * m) + 246 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_246 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 246) < 512 * (2 * m + 1) + 246 := by
  apply refinement_cleared (k := 9) (r := 246) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_246]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 247). -/
theorem data_9_247 : oddCount 247 9 = 5 ∧
    acceleratedOrbit 9 247 = 118 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_247 : gap 9 247 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_247 : threshold 9 247 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_247 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 247) = 243 * (2 * m) + 118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 247
  rw [data_9_247.1, data_9_247.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_247 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 247) = 243 * (2 * m + 1) + 118 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 247
  rw [data_9_247.1, data_9_247.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_247 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 247) < 512 * (2 * m) + 247 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 247 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_247] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 247) < 512 * (2 * m) + 247 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_247 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 247) < 512 * (2 * m + 1) + 247 := by
  apply refinement_cleared (k := 9) (r := 247) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_247]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 248). -/
theorem data_9_248 : oddCount 248 9 = 5 ∧
    acceleratedOrbit 9 248 = 121 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_248 : gap 9 248 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_248 : threshold 9 248 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_248 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 248) = 243 * (2 * m) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 248
  rw [data_9_248.1, data_9_248.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_248 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 248) = 243 * (2 * m + 1) + 121 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 248
  rw [data_9_248.1, data_9_248.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_248 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 248) < 512 * (2 * m) + 248 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 248 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_248] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 248) < 512 * (2 * m) + 248 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_248 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 248) < 512 * (2 * m + 1) + 248 := by
  apply refinement_cleared (k := 9) (r := 248) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_248]; decide

end Collatz.Research.RefinementAtlas.Batch198
