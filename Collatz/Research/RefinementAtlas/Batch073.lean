import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 073. -/
namespace Collatz.Research.RefinementAtlas.Batch073
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 34). -/
theorem data_8_34 : oddCount 34 8 = 3 ∧
    acceleratedOrbit 8 34 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_34 : gap 8 34 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_34 : threshold 8 34 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_34 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 34) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 34
  rw [data_8_34.1, data_8_34.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_34 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 34) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 34
  rw [data_8_34.1, data_8_34.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_34 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 34) < 256 * (2 * m) + 34 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 34 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_34] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 34) < 256 * (2 * m) + 34 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_34 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 34) < 256 * (2 * m + 1) + 34 := by
  apply refinement_cleared (k := 8) (r := 34) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_34]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 35). -/
theorem data_8_35 : oddCount 35 8 = 3 ∧
    acceleratedOrbit 8 35 = 4 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_35 : gap 8 35 = 229 ∧ 27 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_35 : threshold 8 35 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_35 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 35) = 27 * (2 * m) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 35
  rw [data_8_35.1, data_8_35.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_35 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 35) = 27 * (2 * m + 1) + 4 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 35
  rw [data_8_35.1, data_8_35.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_35 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 35) < 256 * (2 * m) + 35 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 35 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_35] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 35) < 256 * (2 * m) + 35 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_35 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 35) < 256 * (2 * m + 1) + 35 := by
  apply refinement_cleared (k := 8) (r := 35) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_35]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 36). -/
theorem data_8_36 : oddCount 36 8 = 4 ∧
    acceleratedOrbit 8 36 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_36 : gap 8 36 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_36 : threshold 8 36 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_36 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 36) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 36
  rw [data_8_36.1, data_8_36.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_36 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 36) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 36
  rw [data_8_36.1, data_8_36.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_36 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 36) < 256 * (2 * m) + 36 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 36 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_36] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 36) < 256 * (2 * m) + 36 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_36 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 36) < 256 * (2 * m + 1) + 36 := by
  apply refinement_cleared (k := 8) (r := 36) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_36]; decide

end Collatz.Research.RefinementAtlas.Batch073
