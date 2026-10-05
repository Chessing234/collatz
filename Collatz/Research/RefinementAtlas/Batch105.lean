import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 105. -/
namespace Collatz.Research.RefinementAtlas.Batch105
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 146). -/
theorem data_8_146 : oddCount 146 8 = 4 ∧
    acceleratedOrbit 8 146 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_146 : gap 8 146 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_146 : threshold 8 146 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_146 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 146) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 146
  rw [data_8_146.1, data_8_146.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_146 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 146) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 146
  rw [data_8_146.1, data_8_146.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_146 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 146) < 256 * (2 * m) + 146 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 146 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_146] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 146) < 256 * (2 * m) + 146 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_146 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 146) < 256 * (2 * m + 1) + 146 := by
  apply refinement_cleared (k := 8) (r := 146) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_146]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 147). -/
theorem data_8_147 : oddCount 147 8 = 4 ∧
    acceleratedOrbit 8 147 = 47 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_147 : gap 8 147 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_147 : threshold 8 147 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_147 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 147) = 81 * (2 * m) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 147
  rw [data_8_147.1, data_8_147.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_147 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 147) = 81 * (2 * m + 1) + 47 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 147
  rw [data_8_147.1, data_8_147.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_147 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 147) < 256 * (2 * m) + 147 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 147 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_147] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 147) < 256 * (2 * m) + 147 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_147 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 147) < 256 * (2 * m + 1) + 147 := by
  apply refinement_cleared (k := 8) (r := 147) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_147]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 148). -/
theorem data_8_148 : oddCount 148 8 = 3 ∧
    acceleratedOrbit 8 148 = 17 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_148 : gap 8 148 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_148 : threshold 8 148 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_148 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 148) = 27 * (2 * m) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 148
  rw [data_8_148.1, data_8_148.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_148 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 148) = 27 * (2 * m + 1) + 17 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 148
  rw [data_8_148.1, data_8_148.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_148 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 148) < 256 * (2 * m) + 148 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 148 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_148] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 148) < 256 * (2 * m) + 148 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_148 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 148) < 256 * (2 * m + 1) + 148 := by
  apply refinement_cleared (k := 8) (r := 148) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_148]; decide

end Collatz.Research.RefinementAtlas.Batch105
