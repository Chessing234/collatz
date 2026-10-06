import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 044. -/
namespace Collatz.Research.RefinementAtlas.Batch044
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 40). -/
theorem data_7_40 : oddCount 40 7 = 1 ∧
    acceleratedOrbit 7 40 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_40 : gap 7 40 = 125 ∧ 3 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_40 : threshold 7 40 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_40 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 40) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 40
  rw [data_7_40.1, data_7_40.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_40 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 40) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 40
  rw [data_7_40.1, data_7_40.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_40 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 40) < 128 * (2 * m) + 40 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 40 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_40] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 40) < 128 * (2 * m) + 40 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_40 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 40) < 128 * (2 * m + 1) + 40 := by
  apply refinement_cleared (k := 7) (r := 40) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_40]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 42). -/
theorem data_7_42 : oddCount 42 7 = 1 ∧
    acceleratedOrbit 7 42 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_42 : gap 7 42 = 125 ∧ 3 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_42 : threshold 7 42 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_42 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 42) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 42
  rw [data_7_42.1, data_7_42.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_42 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 42) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 42
  rw [data_7_42.1, data_7_42.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_42 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 42) < 128 * (2 * m) + 42 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 42 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_42] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 42) < 128 * (2 * m) + 42 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_42 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 42) < 128 * (2 * m + 1) + 42 := by
  apply refinement_cleared (k := 7) (r := 42) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_42]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 43). -/
theorem data_7_43 : oddCount 43 7 = 4 ∧
    acceleratedOrbit 7 43 = 28 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_43 : gap 7 43 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_43 : threshold 7 43 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_43 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 43) = 81 * (2 * m) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 43
  rw [data_7_43.1, data_7_43.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_43 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 43) = 81 * (2 * m + 1) + 28 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 43
  rw [data_7_43.1, data_7_43.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_43 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 43) < 128 * (2 * m) + 43 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 43 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_43] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 43) < 128 * (2 * m) + 43 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_43 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 43) < 128 * (2 * m + 1) + 43 := by
  apply refinement_cleared (k := 7) (r := 43) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_43]; decide

end Collatz.Research.RefinementAtlas.Batch044
