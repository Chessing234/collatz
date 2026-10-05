import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 087. -/
namespace Collatz.Research.RefinementAtlas.Batch087
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 85). -/
theorem data_8_85 : oddCount 85 8 = 1 ∧
    acceleratedOrbit 8 85 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_85 : gap 8 85 = 253 ∧ 3 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_85 : threshold 8 85 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_85 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 85) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 85
  rw [data_8_85.1, data_8_85.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_85 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 85) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 85
  rw [data_8_85.1, data_8_85.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_85 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 85) < 256 * (2 * m) + 85 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 85 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_85] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 85) < 256 * (2 * m) + 85 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_85 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 85) < 256 * (2 * m + 1) + 85 := by
  apply refinement_cleared (k := 8) (r := 85) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_85]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 86). -/
theorem data_8_86 : oddCount 86 8 = 4 ∧
    acceleratedOrbit 8 86 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_86 : gap 8 86 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_86 : threshold 8 86 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_86 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 86) = 81 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 86
  rw [data_8_86.1, data_8_86.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_86 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 86) = 81 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 86
  rw [data_8_86.1, data_8_86.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_86 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 86) < 256 * (2 * m) + 86 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 86 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_86] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 86) < 256 * (2 * m) + 86 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_86 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 86) < 256 * (2 * m + 1) + 86 := by
  apply refinement_cleared (k := 8) (r := 86) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_86]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 87). -/
theorem data_8_87 : oddCount 87 8 = 4 ∧
    acceleratedOrbit 8 87 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_87 : gap 8 87 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_87 : threshold 8 87 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_87 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 87) = 81 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 87
  rw [data_8_87.1, data_8_87.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_87 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 87) = 81 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 87
  rw [data_8_87.1, data_8_87.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_87 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 87) < 256 * (2 * m) + 87 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 87 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_87] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 87) < 256 * (2 * m) + 87 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_87 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 87) < 256 * (2 * m + 1) + 87 := by
  apply refinement_cleared (k := 8) (r := 87) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_87]; decide

end Collatz.Research.RefinementAtlas.Batch087
