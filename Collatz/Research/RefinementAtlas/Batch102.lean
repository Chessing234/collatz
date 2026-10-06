import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 102. -/
namespace Collatz.Research.RefinementAtlas.Batch102
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 136). -/
theorem data_8_136 : oddCount 136 8 = 2 ∧
    acceleratedOrbit 8 136 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_136 : gap 8 136 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_136 : threshold 8 136 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_136 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 136) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 136
  rw [data_8_136.1, data_8_136.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_136 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 136) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 136
  rw [data_8_136.1, data_8_136.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_136 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 136) < 256 * (2 * m) + 136 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 136 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_136] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 136) < 256 * (2 * m) + 136 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_136 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 136) < 256 * (2 * m + 1) + 136 := by
  apply refinement_cleared (k := 8) (r := 136) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_136]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 138). -/
theorem data_8_138 : oddCount 138 8 = 2 ∧
    acceleratedOrbit 8 138 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_138 : gap 8 138 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_138 : threshold 8 138 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_138 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 138) = 9 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 138
  rw [data_8_138.1, data_8_138.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_138 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 138) = 9 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 138
  rw [data_8_138.1, data_8_138.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_138 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 138) < 256 * (2 * m) + 138 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 138 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_138] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 138) < 256 * (2 * m) + 138 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_138 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 138) < 256 * (2 * m + 1) + 138 := by
  apply refinement_cleared (k := 8) (r := 138) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_138]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 139). -/
theorem data_8_139 : oddCount 139 8 = 5 ∧
    acceleratedOrbit 8 139 = 134 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_139 : gap 8 139 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_139 : threshold 8 139 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_139 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 139) = 243 * (2 * m) + 134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 139
  rw [data_8_139.1, data_8_139.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_139 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 139) = 243 * (2 * m + 1) + 134 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 139
  rw [data_8_139.1, data_8_139.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_139 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 139) < 256 * (2 * m) + 139 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 139 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_139] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 139) < 256 * (2 * m) + 139 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_139 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 139) < 256 * (2 * m + 1) + 139 := by
  apply refinement_cleared (k := 8) (r := 139) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_139]; decide

end Collatz.Research.RefinementAtlas.Batch102
