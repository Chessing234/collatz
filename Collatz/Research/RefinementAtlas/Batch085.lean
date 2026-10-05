import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 085. -/
namespace Collatz.Research.RefinementAtlas.Batch085
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 77). -/
theorem data_8_77 : oddCount 77 8 = 4 ∧
    acceleratedOrbit 8 77 = 26 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_77 : gap 8 77 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_77 : threshold 8 77 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_77 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 77) = 81 * (2 * m) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 77
  rw [data_8_77.1, data_8_77.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_77 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 77) = 81 * (2 * m + 1) + 26 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 77
  rw [data_8_77.1, data_8_77.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_77 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 77) < 256 * (2 * m) + 77 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 77 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_77] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 77) < 256 * (2 * m) + 77 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_77 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 77) < 256 * (2 * m + 1) + 77 := by
  apply refinement_cleared (k := 8) (r := 77) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_77]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 78). -/
theorem data_8_78 : oddCount 78 8 = 5 ∧
    acceleratedOrbit 8 78 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_78 : gap 8 78 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_78 : threshold 8 78 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_78 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 78) = 243 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 78
  rw [data_8_78.1, data_8_78.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_78 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 78) = 243 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 78
  rw [data_8_78.1, data_8_78.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_78 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 78) < 256 * (2 * m) + 78 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 78 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_78] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 78) < 256 * (2 * m) + 78 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_78 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 78) < 256 * (2 * m + 1) + 78 := by
  apply refinement_cleared (k := 8) (r := 78) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_78]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 79). -/
theorem data_8_79 : oddCount 79 8 = 5 ∧
    acceleratedOrbit 8 79 = 76 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_79 : gap 8 79 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_79 : threshold 8 79 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_79 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 79) = 243 * (2 * m) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 79
  rw [data_8_79.1, data_8_79.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_79 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 79) = 243 * (2 * m + 1) + 76 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 79
  rw [data_8_79.1, data_8_79.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_79 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 79) < 256 * (2 * m) + 79 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 79 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_79] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 79) < 256 * (2 * m) + 79 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_79 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 79) < 256 * (2 * m + 1) + 79 := by
  apply refinement_cleared (k := 8) (r := 79) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_79]; decide

end Collatz.Research.RefinementAtlas.Batch085
