import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 175. -/
namespace Collatz.Research.RefinementAtlas.Batch175
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (9, 152). -/
theorem data_9_152 : oddCount 152 9 = 4 ∧
    acceleratedOrbit 9 152 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_152 : gap 9 152 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_152 : threshold 9 152 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_152 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 152) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 152
  rw [data_9_152.1, data_9_152.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_152 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 152) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 152
  rw [data_9_152.1, data_9_152.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_152 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 152) < 512 * (2 * m) + 152 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 152 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_152] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 152) < 512 * (2 * m) + 152 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_152 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 152) < 512 * (2 * m + 1) + 152 := by
  apply refinement_cleared (k := 9) (r := 152) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_152]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 153). -/
theorem data_9_153 : oddCount 153 9 = 5 ∧
    acceleratedOrbit 9 153 = 74 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_153 : gap 9 153 = 269 ∧ 243 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_153 : threshold 9 153 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_153 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 153) = 243 * (2 * m) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 153
  rw [data_9_153.1, data_9_153.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_153 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 153) = 243 * (2 * m + 1) + 74 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 153
  rw [data_9_153.1, data_9_153.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_153 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 153) < 512 * (2 * m) + 153 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 153 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_153] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 153) < 512 * (2 * m) + 153 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_153 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 153) < 512 * (2 * m + 1) + 153 := by
  apply refinement_cleared (k := 9) (r := 153) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_153]; decide

/-- Kernel-evaluated parity count and endpoint for (9, 154). -/
theorem data_9_154 : oddCount 154 9 = 4 ∧
    acceleratedOrbit 9 154 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_9_154 : gap 9 154 = 431 ∧ 81 < 512 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_9_154 : threshold 9 154 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_9_154 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 154) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m) 154
  rw [data_9_154.1, data_9_154.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_9_154 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 154) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 9 (2 * m + 1) 154
  rw [data_9_154.1, data_9_154.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_9_154 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m) + 154) < 512 * (2 * m) + 154 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 154 9 < 2 ^ 9 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_9_154] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 9 (512 * (2 * m) + 154) < 512 * (2 * m) + 154 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_9_154 (m : Nat) :
    acceleratedOrbit 9 (512 * (2 * m + 1) + 154) < 512 * (2 * m + 1) + 154 := by
  apply refinement_cleared (k := 9) (r := 154) (s := 2) (q := 1)
  · decide
  · rw [cutoff_9_154]; decide

end Collatz.Research.RefinementAtlas.Batch175
