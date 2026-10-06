import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 114. -/
namespace Collatz.Research.RefinementAtlas.Batch114
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 177). -/
theorem data_8_177 : oddCount 177 8 = 3 ∧
    acceleratedOrbit 8 177 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_177 : gap 8 177 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_177 : threshold 8 177 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_177 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 177) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 177
  rw [data_8_177.1, data_8_177.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_177 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 177) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 177
  rw [data_8_177.1, data_8_177.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_177 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 177) < 256 * (2 * m) + 177 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 177 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_177] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 177) < 256 * (2 * m) + 177 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_177 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 177) < 256 * (2 * m + 1) + 177 := by
  apply refinement_cleared (k := 8) (r := 177) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_177]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 178). -/
theorem data_8_178 : oddCount 178 8 = 3 ∧
    acceleratedOrbit 8 178 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_178 : gap 8 178 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_178 : threshold 8 178 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_178 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 178) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 178
  rw [data_8_178.1, data_8_178.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_178 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 178) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 178
  rw [data_8_178.1, data_8_178.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_178 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 178) < 256 * (2 * m) + 178 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 178 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_178] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 178) < 256 * (2 * m) + 178 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_178 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 178) < 256 * (2 * m + 1) + 178 := by
  apply refinement_cleared (k := 8) (r := 178) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_178]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 179). -/
theorem data_8_179 : oddCount 179 8 = 3 ∧
    acceleratedOrbit 8 179 = 19 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_179 : gap 8 179 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_179 : threshold 8 179 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_179 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 179) = 27 * (2 * m) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 179
  rw [data_8_179.1, data_8_179.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_179 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 179) = 27 * (2 * m + 1) + 19 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 179
  rw [data_8_179.1, data_8_179.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_179 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 179) < 256 * (2 * m) + 179 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 179 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_179] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 179) < 256 * (2 * m) + 179 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_179 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 179) < 256 * (2 * m + 1) + 179 := by
  apply refinement_cleared (k := 8) (r := 179) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_179]; decide

end Collatz.Research.RefinementAtlas.Batch114
