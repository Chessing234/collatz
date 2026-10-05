import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 038. -/
namespace Collatz.Research.RefinementAtlas.Batch038
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 19). -/
theorem data_7_19 : oddCount 19 7 = 4 ∧
    acceleratedOrbit 7 19 = 13 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_19 : gap 7 19 = 47 ∧ 81 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_19 : threshold 7 19 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_19 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 19) = 81 * (2 * m) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 19
  rw [data_7_19.1, data_7_19.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_19 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 19) = 81 * (2 * m + 1) + 13 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 19
  rw [data_7_19.1, data_7_19.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_19 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 19) < 128 * (2 * m) + 19 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 19 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_19] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 19) < 128 * (2 * m) + 19 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_19 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 19) < 128 * (2 * m + 1) + 19 := by
  apply refinement_cleared (k := 7) (r := 19) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_19]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 20). -/
theorem data_7_20 : oddCount 20 7 = 2 ∧
    acceleratedOrbit 7 20 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_20 : gap 7 20 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_20 : threshold 7 20 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_20 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 20) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 20
  rw [data_7_20.1, data_7_20.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_20 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 20) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 20
  rw [data_7_20.1, data_7_20.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_20 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 20) < 128 * (2 * m) + 20 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 20 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_20] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 20) < 128 * (2 * m) + 20 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_20 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 20) < 128 * (2 * m + 1) + 20 := by
  apply refinement_cleared (k := 7) (r := 20) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_20]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 21). -/
theorem data_7_21 : oddCount 21 7 = 2 ∧
    acceleratedOrbit 7 21 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_21 : gap 7 21 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_21 : threshold 7 21 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_21 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 21) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 21
  rw [data_7_21.1, data_7_21.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_21 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 21) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 21
  rw [data_7_21.1, data_7_21.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_21 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 21) < 128 * (2 * m) + 21 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 21 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_21] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 21) < 128 * (2 * m) + 21 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_21 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 21) < 128 * (2 * m + 1) + 21 := by
  apply refinement_cleared (k := 7) (r := 21) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_21]; decide

end Collatz.Research.RefinementAtlas.Batch038
