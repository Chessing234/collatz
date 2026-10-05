import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 134. -/
namespace Collatz.Research.RefinementAtlas.Batch134
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 247). -/
theorem data_8_247 : oddCount 247 8 = 5 ∧
    acceleratedOrbit 8 247 = 236 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_247 : gap 8 247 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_247 : threshold 8 247 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_247 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 247) = 243 * (2 * m) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 247
  rw [data_8_247.1, data_8_247.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_247 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 247) = 243 * (2 * m + 1) + 236 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 247
  rw [data_8_247.1, data_8_247.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_247 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 247) < 256 * (2 * m) + 247 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 247 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_247] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 247) < 256 * (2 * m) + 247 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_247 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 247) < 256 * (2 * m + 1) + 247 := by
  apply refinement_cleared (k := 8) (r := 247) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_247]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 248). -/
theorem data_8_248 : oddCount 248 8 = 5 ∧
    acceleratedOrbit 8 248 = 242 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_248 : gap 8 248 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_248 : threshold 8 248 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_248 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 248) = 243 * (2 * m) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 248
  rw [data_8_248.1, data_8_248.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_248 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 248) = 243 * (2 * m + 1) + 242 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 248
  rw [data_8_248.1, data_8_248.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_248 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 248) < 256 * (2 * m) + 248 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 248 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_248] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 248) < 256 * (2 * m) + 248 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_248 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 248) < 256 * (2 * m + 1) + 248 := by
  apply refinement_cleared (k := 8) (r := 248) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_248]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 249). -/
theorem data_8_249 : oddCount 249 8 = 5 ∧
    acceleratedOrbit 8 249 = 238 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_249 : gap 8 249 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_249 : threshold 8 249 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_249 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 249) = 243 * (2 * m) + 238 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 249
  rw [data_8_249.1, data_8_249.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_249 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 249) = 243 * (2 * m + 1) + 238 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 249
  rw [data_8_249.1, data_8_249.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_249 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 249) < 256 * (2 * m) + 249 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 249 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_249] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 249) < 256 * (2 * m) + 249 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_249 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 249) < 256 * (2 * m + 1) + 249 := by
  apply refinement_cleared (k := 8) (r := 249) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_249]; decide

end Collatz.Research.RefinementAtlas.Batch134
