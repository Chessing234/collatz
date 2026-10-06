import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 180. -/
namespace Collatz.Research.RefinementAtlas.Batch180
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 176). -/
theorem data_9_176 : oddCount 176 9 = 3 ∧
    acceleratedOrbit 9 176 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_176 : gap 9 176 = 485 ∧ 27 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_176 : threshold 9 176 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_176 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 176) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 176
  rw [data_9_176.1, data_9_176.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_176 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 176) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 176
  rw [data_9_176.1, data_9_176.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_176 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 176) < 512 * (2 * m) + 176 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 176 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_176] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 176) < 512 * (2 * m) + 176 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_176 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 176) < 512 * (2 * m + 1) + 176 := by
  apply refinement_cleared (k := 9) (r := 176) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_176]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 177). -/
theorem data_9_177 : oddCount 177 9 = 4 ∧
    acceleratedOrbit 9 177 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_177 : gap 9 177 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_177 : threshold 9 177 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_177 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 177) = 81 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 177
  rw [data_9_177.1, data_9_177.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_177 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 177) = 81 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 177
  rw [data_9_177.1, data_9_177.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_177 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 177) < 512 * (2 * m) + 177 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 177 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_177] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 177) < 512 * (2 * m) + 177 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_177 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 177) < 512 * (2 * m + 1) + 177 := by
  apply refinement_cleared (k := 9) (r := 177) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_177]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 178). -/
theorem data_9_178 : oddCount 178 9 = 4 ∧
    acceleratedOrbit 9 178 = 29 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_178 : gap 9 178 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_178 : threshold 9 178 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_178 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 178) = 81 * (2 * m) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 178
  rw [data_9_178.1, data_9_178.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_178 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 178) = 81 * (2 * m + 1) + 29 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 178
  rw [data_9_178.1, data_9_178.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_178 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 178) < 512 * (2 * m) + 178 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 178 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_178] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 178) < 512 * (2 * m) + 178 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_178 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 178) < 512 * (2 * m + 1) + 178 := by
  apply refinement_cleared (k := 9) (r := 178) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_178]; decide

end Collatz.Research.RefinementAtlas.Batch180
