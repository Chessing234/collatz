import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 108. -/
namespace Collatz.Research.RefinementAtlas.Batch108
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 156). -/
theorem data_8_156 : oddCount 156 8 = 5 ∧
    acceleratedOrbit 8 156 = 152 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_156 : gap 8 156 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_156 : threshold 8 156 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_156 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 156) = 243 * (2 * m) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 156
  rw [data_8_156.1, data_8_156.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_156 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 156) = 243 * (2 * m + 1) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 156
  rw [data_8_156.1, data_8_156.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_156 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 156) < 256 * (2 * m) + 156 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 156 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_156] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 156) < 256 * (2 * m) + 156 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_156 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 156) < 256 * (2 * m + 1) + 156 := by
  apply refinement_cleared (k := 8) (r := 156) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_156]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 157). -/
theorem data_8_157 : oddCount 157 8 = 5 ∧
    acceleratedOrbit 8 157 = 152 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_157 : gap 8 157 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_157 : threshold 8 157 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_157 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 157) = 243 * (2 * m) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 157
  rw [data_8_157.1, data_8_157.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_157 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 157) = 243 * (2 * m + 1) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 157
  rw [data_8_157.1, data_8_157.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_157 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 157) < 256 * (2 * m) + 157 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 157 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_157] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 157) < 256 * (2 * m) + 157 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_157 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 157) < 256 * (2 * m + 1) + 157 := by
  apply refinement_cleared (k := 8) (r := 157) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_157]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 158). -/
theorem data_8_158 : oddCount 158 8 = 5 ∧
    acceleratedOrbit 8 158 = 152 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_158 : gap 8 158 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_158 : threshold 8 158 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_158 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 158) = 243 * (2 * m) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 158
  rw [data_8_158.1, data_8_158.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_158 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 158) = 243 * (2 * m + 1) + 152 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 158
  rw [data_8_158.1, data_8_158.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_158 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 158) < 256 * (2 * m) + 158 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 158 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_158] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 158) < 256 * (2 * m) + 158 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_158 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 158) < 256 * (2 * m + 1) + 158 := by
  apply refinement_cleared (k := 8) (r := 158) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_158]; decide

end Collatz.Research.RefinementAtlas.Batch108
