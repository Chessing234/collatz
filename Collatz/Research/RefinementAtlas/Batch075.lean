import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 075. -/
namespace Collatz.Research.RefinementAtlas.Batch075
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (8, 40). -/
theorem data_8_40 : oddCount 40 8 = 2 ∧
    acceleratedOrbit 8 40 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_40 : gap 8 40 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_40 : threshold 8 40 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_40 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 40) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 40
  rw [data_8_40.1, data_8_40.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_40 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 40) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 40
  rw [data_8_40.1, data_8_40.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_40 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 40) < 256 * (2 * m) + 40 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 40 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_40] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 40) < 256 * (2 * m) + 40 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_40 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 40) < 256 * (2 * m + 1) + 40 := by
  apply refinement_cleared (k := 8) (r := 40) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_40]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 42). -/
theorem data_8_42 : oddCount 42 8 = 2 ∧
    acceleratedOrbit 8 42 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_42 : gap 8 42 = 247 ∧ 9 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_42 : threshold 8 42 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_42 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 42) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 42
  rw [data_8_42.1, data_8_42.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_42 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 42) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 42
  rw [data_8_42.1, data_8_42.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_42 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 42) < 256 * (2 * m) + 42 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 42 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_42] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 42) < 256 * (2 * m) + 42 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_42 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 42) < 256 * (2 * m + 1) + 42 := by
  apply refinement_cleared (k := 8) (r := 42) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_42]; decide

/-- Kernel-evaluated parity count and endpoint for (8, 43). -/
theorem data_8_43 : oddCount 43 8 = 4 ∧
    acceleratedOrbit 8 43 = 14 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_8_43 : gap 8 43 = 175 ∧ 81 < 256 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_8_43 : threshold 8 43 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_8_43 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 43) = 81 * (2 * m) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m) 43
  rw [data_8_43.1, data_8_43.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_8_43 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 43) = 81 * (2 * m + 1) + 14 := by
  have h := Congruence.accOrbit_pow_two_mul_add 8 (2 * m + 1) 43
  rw [data_8_43.1, data_8_43.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_8_43 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m) + 43) < 256 * (2 * m) + 43 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 43 8 < 2 ^ 8 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_8_43] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 8 (256 * (2 * m) + 43) < 256 * (2 * m) + 43 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_8_43 (m : Nat) :
    acceleratedOrbit 8 (256 * (2 * m + 1) + 43) < 256 * (2 * m + 1) + 43 := by
  apply refinement_cleared (k := 8) (r := 43) (s := 2) (q := 1)
  · decide
  · rw [cutoff_8_43]; decide

end Collatz.Research.RefinementAtlas.Batch075
