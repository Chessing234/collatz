import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 071. -/
namespace Collatz.Research.RefinementAtlas.Batch071
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 26). -/
theorem data_8_26 : oddCount 26 8 = 2 ∧
    acceleratedOrbit 8 26 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_26 : gap 8 26 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_26 : threshold 8 26 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_26 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 26) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 26
  rw [data_8_26.1, data_8_26.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_26 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 26) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 26
  rw [data_8_26.1, data_8_26.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_26 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 26) < 256 * (2 * m) + 26 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 26 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_26] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 26) < 256 * (2 * m) + 26 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_26 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 26) < 256 * (2 * m + 1) + 26 := by
  apply refinement_cleared (k := 8) (r := 26) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_26]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 28). -/
theorem data_8_28 : oddCount 28 8 = 4 ∧
    acceleratedOrbit 8 28 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_28 : gap 8 28 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_28 : threshold 8 28 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_28 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 28) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 28
  rw [data_8_28.1, data_8_28.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_28 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 28) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 28
  rw [data_8_28.1, data_8_28.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_28 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 28) < 256 * (2 * m) + 28 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 28 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_28] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 28) < 256 * (2 * m) + 28 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_28 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 28) < 256 * (2 * m + 1) + 28 := by
  apply refinement_cleared (k := 8) (r := 28) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_28]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 29). -/
theorem data_8_29 : oddCount 29 8 = 4 ∧
    acceleratedOrbit 8 29 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_29 : gap 8 29 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_29 : threshold 8 29 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_29 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 29) = 81 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 29
  rw [data_8_29.1, data_8_29.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_29 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 29) = 81 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 29
  rw [data_8_29.1, data_8_29.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_29 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 29) < 256 * (2 * m) + 29 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 29 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_29] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 29) < 256 * (2 * m) + 29 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_29 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 29) < 256 * (2 * m + 1) + 29 := by
  apply refinement_cleared (k := 8) (r := 29) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_29]; decide

end Collatz.Research.RefinementAtlas.Batch071
