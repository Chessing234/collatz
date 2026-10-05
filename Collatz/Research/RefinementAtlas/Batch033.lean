import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 033. -/
namespace Collatz.Research.RefinementAtlas.Batch033
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (7, 3). -/
theorem data_7_3 : oddCount 3 7 = 3 ∧
    acceleratedOrbit 7 3 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_3 : gap 7 3 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_3 : threshold 7 3 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_3 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 3) = 27 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 3
  rw [data_7_3.1, data_7_3.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_3 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 3) = 27 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 3
  rw [data_7_3.1, data_7_3.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_3 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 3) < 128 * (2 * m) + 3 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 3 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_3] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 3) < 128 * (2 * m) + 3 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_3 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 3) < 128 * (2 * m + 1) + 3 := by
  apply refinement_cleared (k := 7) (r := 3) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_3]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 4). -/
theorem data_7_4 : oddCount 4 7 = 3 ∧
    acceleratedOrbit 7 4 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_4 : gap 7 4 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_4 : threshold 7 4 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_4 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 4) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 4
  rw [data_7_4.1, data_7_4.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_4 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 4) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 4
  rw [data_7_4.1, data_7_4.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_4 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 4) < 128 * (2 * m) + 4 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 4 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_4] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 4) < 128 * (2 * m) + 4 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_4 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 4) < 128 * (2 * m + 1) + 4 := by
  apply refinement_cleared (k := 7) (r := 4) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_4]; decide

/-- Kernel-evaluated parity count and endpoint for (7, 5). -/
theorem data_7_5 : oddCount 5 7 = 3 ∧
    acceleratedOrbit 7 5 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_7_5 : gap 7 5 = 101 ∧ 27 < 128 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_7_5 : threshold 7 5 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_7_5 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 5) = 27 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m) 5
  rw [data_7_5.1, data_7_5.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_7_5 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 5) = 27 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 7 (2 * m + 1) 5
  rw [data_7_5.1, data_7_5.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_7_5 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m) + 5) < 128 * (2 * m) + 5 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 5 7 < 2 ^ 7 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_7_5] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 7 (128 * (2 * m) + 5) < 128 * (2 * m) + 5 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_7_5 (m : Nat) :
    acceleratedOrbit 7 (128 * (2 * m + 1) + 5) < 128 * (2 * m + 1) + 5 := by
  apply refinement_cleared (k := 7) (r := 5) (s := 2) (q := 1)
  · decide
  · rw [cutoff_7_5]; decide

end Collatz.Research.RefinementAtlas.Batch033
