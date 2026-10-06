import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 094. -/
namespace Collatz.Research.RefinementAtlas.Batch094
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 108). -/
theorem data_8_108 : oddCount 108 8 = 5 ∧
    acceleratedOrbit 8 108 = 107 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_108 : gap 8 108 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_108 : threshold 8 108 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_108 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 108) = 243 * (2 * m) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 108
  rw [data_8_108.1, data_8_108.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_108 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 108) = 243 * (2 * m + 1) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 108
  rw [data_8_108.1, data_8_108.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_108 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 108) < 256 * (2 * m) + 108 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 108 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_108] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 108) < 256 * (2 * m) + 108 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_108 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 108) < 256 * (2 * m + 1) + 108 := by
  apply refinement_cleared (k := 8) (r := 108) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_108]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 109). -/
theorem data_8_109 : oddCount 109 8 = 5 ∧
    acceleratedOrbit 8 109 = 107 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_109 : gap 8 109 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_109 : threshold 8 109 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_109 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 109) = 243 * (2 * m) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 109
  rw [data_8_109.1, data_8_109.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_109 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 109) = 243 * (2 * m + 1) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 109
  rw [data_8_109.1, data_8_109.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_109 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 109) < 256 * (2 * m) + 109 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 109 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_109] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 109) < 256 * (2 * m) + 109 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_109 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 109) < 256 * (2 * m + 1) + 109 := by
  apply refinement_cleared (k := 8) (r := 109) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_109]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 110). -/
theorem data_8_110 : oddCount 110 8 = 5 ∧
    acceleratedOrbit 8 110 = 107 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_110 : gap 8 110 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_110 : threshold 8 110 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_110 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 110) = 243 * (2 * m) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 110
  rw [data_8_110.1, data_8_110.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_110 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 110) = 243 * (2 * m + 1) + 107 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 110
  rw [data_8_110.1, data_8_110.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_110 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 110) < 256 * (2 * m) + 110 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 110 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_110] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 110) < 256 * (2 * m) + 110 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_110 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 110) < 256 * (2 * m + 1) + 110 := by
  apply refinement_cleared (k := 8) (r := 110) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_110]; decide

end Collatz.Research.RefinementAtlas.Batch094
