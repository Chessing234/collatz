import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 089. -/
namespace Collatz.Research.RefinementAtlas.Batch089
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 92). -/
theorem data_8_92 : oddCount 92 8 = 3 ∧
    acceleratedOrbit 8 92 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_92 : gap 8 92 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_92 : threshold 8 92 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_92 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 92) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 92
  rw [data_8_92.1, data_8_92.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_92 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 92) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 92
  rw [data_8_92.1, data_8_92.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_92 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 92) < 256 * (2 * m) + 92 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 92 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_92] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 92) < 256 * (2 * m) + 92 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_92 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 92) < 256 * (2 * m + 1) + 92 := by
  apply refinement_cleared (k := 8) (r := 92) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_92]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 93). -/
theorem data_8_93 : oddCount 93 8 = 3 ∧
    acceleratedOrbit 8 93 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_93 : gap 8 93 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_93 : threshold 8 93 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_93 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 93) = 27 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 93
  rw [data_8_93.1, data_8_93.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_93 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 93) = 27 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 93
  rw [data_8_93.1, data_8_93.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_93 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 93) < 256 * (2 * m) + 93 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 93 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_93] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 93) < 256 * (2 * m) + 93 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_93 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 93) < 256 * (2 * m + 1) + 93 := by
  apply refinement_cleared (k := 8) (r := 93) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_93]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 94). -/
theorem data_8_94 : oddCount 94 8 = 5 ∧
    acceleratedOrbit 8 94 = 91 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_94 : gap 8 94 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_94 : threshold 8 94 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_94 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 94) = 243 * (2 * m) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 94
  rw [data_8_94.1, data_8_94.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_94 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 94) = 243 * (2 * m + 1) + 91 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 94
  rw [data_8_94.1, data_8_94.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_94 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 94) < 256 * (2 * m) + 94 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 94 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_94] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 94) < 256 * (2 * m) + 94 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_94 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 94) < 256 * (2 * m + 1) + 94 := by
  apply refinement_cleared (k := 8) (r := 94) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_94]; decide

end Collatz.Research.RefinementAtlas.Batch089
