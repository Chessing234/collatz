import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 107. -/
namespace Collatz.Research.RefinementAtlas.Batch107
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 152). -/
theorem data_8_152 : oddCount 152 8 = 3 ∧
    acceleratedOrbit 8 152 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_152 : gap 8 152 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_152 : threshold 8 152 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_152 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 152) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 152
  rw [data_8_152.1, data_8_152.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_152 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 152) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 152
  rw [data_8_152.1, data_8_152.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_152 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 152) < 256 * (2 * m) + 152 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 152 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_152] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 152) < 256 * (2 * m) + 152 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_152 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 152) < 256 * (2 * m + 1) + 152 := by
  apply refinement_cleared (k := 8) (r := 152) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_152]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 153). -/
theorem data_8_153 : oddCount 153 8 = 4 ∧
    acceleratedOrbit 8 153 = 49 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_153 : gap 8 153 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_153 : threshold 8 153 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_153 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 153) = 81 * (2 * m) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 153
  rw [data_8_153.1, data_8_153.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_153 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 153) = 81 * (2 * m + 1) + 49 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 153
  rw [data_8_153.1, data_8_153.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_153 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 153) < 256 * (2 * m) + 153 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 153 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_153] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 153) < 256 * (2 * m) + 153 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_153 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 153) < 256 * (2 * m + 1) + 153 := by
  apply refinement_cleared (k := 8) (r := 153) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_153]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 154). -/
theorem data_8_154 : oddCount 154 8 = 3 ∧
    acceleratedOrbit 8 154 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_154 : gap 8 154 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_154 : threshold 8 154 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_154 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 154) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 154
  rw [data_8_154.1, data_8_154.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_154 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 154) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 154
  rw [data_8_154.1, data_8_154.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_154 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 154) < 256 * (2 * m) + 154 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 154 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_154] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 154) < 256 * (2 * m) + 154 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_154 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 154) < 256 * (2 * m + 1) + 154 := by
  apply refinement_cleared (k := 8) (r := 154) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_154]; decide

end Collatz.Research.RefinementAtlas.Batch107
