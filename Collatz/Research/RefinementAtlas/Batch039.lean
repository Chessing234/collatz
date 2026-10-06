import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 039. -/
namespace Collatz.Research.RefinementAtlas.Batch039
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 22). -/
theorem data_7_22 : oddCount 22 7 = 3 ∧
    acceleratedOrbit 7 22 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_22 : gap 7 22 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_22 : threshold 7 22 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_22 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 22) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 22
  rw [data_7_22.1, data_7_22.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_22 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 22) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 22
  rw [data_7_22.1, data_7_22.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_22 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 22) < 128 * (2 * m) + 22 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 22 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_22] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 22) < 128 * (2 * m) + 22 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_22 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 22) < 128 * (2 * m + 1) + 22 := by
  apply refinement_cleared (k := 7) (r := 22) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_22]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 23). -/
theorem data_7_23 : oddCount 23 7 = 3 ∧
    acceleratedOrbit 7 23 = 5 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_23 : gap 7 23 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_23 : threshold 7 23 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_23 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 23) = 27 * (2 * m) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 23
  rw [data_7_23.1, data_7_23.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_23 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 23) = 27 * (2 * m + 1) + 5 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 23
  rw [data_7_23.1, data_7_23.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_23 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 23) < 128 * (2 * m) + 23 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 23 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_23] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 23) < 128 * (2 * m) + 23 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_23 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 23) < 128 * (2 * m + 1) + 23 := by
  apply refinement_cleared (k := 7) (r := 23) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_23]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 24). -/
theorem data_7_24 : oddCount 24 7 = 2 ∧
    acceleratedOrbit 7 24 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_24 : gap 7 24 = 119 ∧ 9 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_24 : threshold 7 24 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_24 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 24) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 24
  rw [data_7_24.1, data_7_24.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_24 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 24) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 24
  rw [data_7_24.1, data_7_24.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_24 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 24) < 128 * (2 * m) + 24 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 24 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_24] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 24) < 128 * (2 * m) + 24 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_24 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 24) < 128 * (2 * m + 1) + 24 := by
  apply refinement_cleared (k := 7) (r := 24) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_24]; decide

end Collatz.Research.RefinementAtlas.Batch039
