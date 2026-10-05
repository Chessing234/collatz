import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 004. -/
namespace Collatz.Research.RefinementAtlas.Batch004
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 2). -/
theorem data_8_2 : oddCount 2 8 = 4 ∧
    acceleratedOrbit 8 2 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_2 : gap 8 2 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_2 : threshold 8 2 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_2 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 2) = 81 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 2
  rw [data_8_2.1, data_8_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_2 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 2) = 81 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 2
  rw [data_8_2.1, data_8_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_2 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 2) < 256 * (2 * m) + 2 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 2 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 2) < 256 * (2 * m) + 2 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_2 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 2) < 256 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 8) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_2]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 7). -/
theorem data_8_7 : oddCount 7 8 = 5 ∧
    acceleratedOrbit 8 7 = 8 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_7 : gap 8 7 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_7 : threshold 8 7 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_7 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 7) = 243 * (2 * m) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 7
  rw [data_8_7.1, data_8_7.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_7 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 7) = 243 * (2 * m + 1) + 8 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 7
  rw [data_8_7.1, data_8_7.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_7 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 7) < 256 * (2 * m) + 7 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 7 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_7] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 7) < 256 * (2 * m) + 7 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_7 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 7) < 256 * (2 * m + 1) + 7 := by
  apply refinement_cleared (k := 8) (r := 7) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_7]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 9). -/
theorem data_8_9 : oddCount 9 8 = 5 ∧
    acceleratedOrbit 8 9 = 10 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_9 : gap 8 9 = 13 ∧ 243 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_9 : threshold 8 9 = 1 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_9 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 9) = 243 * (2 * m) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 9
  rw [data_8_9.1, data_8_9.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_9 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 9) = 243 * (2 * m + 1) + 10 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 9
  rw [data_8_9.1, data_8_9.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_9 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 9) < 256 * (2 * m) + 9 ↔ 1 ≤ m := by
  have hc : 3 ^ oddCount 9 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_9] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 9) < 256 * (2 * m) + 9 ↔ 1 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_9 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 9) < 256 * (2 * m + 1) + 9 := by
  apply refinement_cleared (k := 8) (r := 9) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_9]; decide

end Collatz.Research.RefinementAtlas.Batch004
