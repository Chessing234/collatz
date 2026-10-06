import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 101. -/
namespace Collatz.Research.RefinementAtlas.Batch101
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 133). -/
theorem data_8_133 : oddCount 133 8 = 4 ∧
    acceleratedOrbit 8 133 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_133 : gap 8 133 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_133 : threshold 8 133 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_133 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 133) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 133
  rw [data_8_133.1, data_8_133.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_133 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 133) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 133
  rw [data_8_133.1, data_8_133.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_133 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 133) < 256 * (2 * m) + 133 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 133 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_133] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 133) < 256 * (2 * m) + 133 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_133 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 133) < 256 * (2 * m + 1) + 133 := by
  apply refinement_cleared (k := 8) (r := 133) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_133]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 134). -/
theorem data_8_134 : oddCount 134 8 = 4 ∧
    acceleratedOrbit 8 134 = 44 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_134 : gap 8 134 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_134 : threshold 8 134 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_134 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 134) = 81 * (2 * m) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 134
  rw [data_8_134.1, data_8_134.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_134 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 134) = 81 * (2 * m + 1) + 44 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 134
  rw [data_8_134.1, data_8_134.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_134 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 134) < 256 * (2 * m) + 134 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 134 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_134] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 134) < 256 * (2 * m) + 134 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_134 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 134) < 256 * (2 * m + 1) + 134 := by
  apply refinement_cleared (k := 8) (r := 134) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_134]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 135). -/
theorem data_8_135 : oddCount 135 8 = 4 ∧
    acceleratedOrbit 8 135 = 43 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_135 : gap 8 135 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_135 : threshold 8 135 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_135 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 135) = 81 * (2 * m) + 43 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 135
  rw [data_8_135.1, data_8_135.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_135 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 135) = 81 * (2 * m + 1) + 43 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 135
  rw [data_8_135.1, data_8_135.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_135 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 135) < 256 * (2 * m) + 135 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 135 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_135] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 135) < 256 * (2 * m) + 135 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_135 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 135) < 256 * (2 * m + 1) + 135 := by
  apply refinement_cleared (k := 8) (r := 135) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_135]; decide

end Collatz.Research.RefinementAtlas.Batch101
