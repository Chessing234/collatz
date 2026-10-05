import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 008. -/
namespace Collatz.Research.RefinementAtlas.Batch008
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (3, 2). -/
theorem data_3_2 : oddCount 2 3 = 1 ∧
    acceleratedOrbit 3 2 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_3_2 : gap 3 2 = 5 ∧ 3 < 8 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_3_2 : threshold 3 2 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_3_2 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m) + 2) = 3 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 3 (2 * m) 2
  rw [data_3_2.1, data_3_2.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_3_2 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m + 1) + 2) = 3 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 3 (2 * m + 1) 2
  rw [data_3_2.1, data_3_2.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_3_2 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m) + 2) < 8 * (2 * m) + 2 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 2 3 < 2 ^ 3 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_3_2] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 3 (8 * (2 * m) + 2) < 8 * (2 * m) + 2 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_3_2 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m + 1) + 2) < 8 * (2 * m + 1) + 2 := by
  apply refinement_cleared (k := 3) (r := 2) (s := 2) (q := 1)
  · decide
  · rw [cutoff_3_2]; decide

/-- Kernel-evaluated parity count and endpoint for (3, 4). -/
theorem data_3_4 : oddCount 4 3 = 1 ∧
    acceleratedOrbit 3 4 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_3_4 : gap 3 4 = 5 ∧ 3 < 8 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_3_4 : threshold 3 4 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_3_4 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m) + 4) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 3 (2 * m) 4
  rw [data_3_4.1, data_3_4.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_3_4 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m + 1) + 4) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 3 (2 * m + 1) 4
  rw [data_3_4.1, data_3_4.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_3_4 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m) + 4) < 8 * (2 * m) + 4 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 4 3 < 2 ^ 3 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_3_4] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 3 (8 * (2 * m) + 4) < 8 * (2 * m) + 4 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_3_4 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m + 1) + 4) < 8 * (2 * m + 1) + 4 := by
  apply refinement_cleared (k := 3) (r := 4) (s := 2) (q := 1)
  · decide
  · rw [cutoff_3_4]; decide

/-- Kernel-evaluated parity count and endpoint for (3, 5). -/
theorem data_3_5 : oddCount 5 3 = 1 ∧
    acceleratedOrbit 3 5 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_3_5 : gap 3 5 = 5 ∧ 3 < 8 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_3_5 : threshold 3 5 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_3_5 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m) + 5) = 3 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 3 (2 * m) 5
  rw [data_3_5.1, data_3_5.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_3_5 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m + 1) + 5) = 3 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 3 (2 * m + 1) 5
  rw [data_3_5.1, data_3_5.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_3_5 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m) + 5) < 8 * (2 * m) + 5 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 5 3 < 2 ^ 3 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_3_5] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 3 (8 * (2 * m) + 5) < 8 * (2 * m) + 5 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_3_5 (m : Nat) :
    acceleratedOrbit 3 (8 * (2 * m + 1) + 5) < 8 * (2 * m + 1) + 5 := by
  apply refinement_cleared (k := 3) (r := 5) (s := 2) (q := 1)
  · decide
  · rw [cutoff_3_5]; decide

end Collatz.Research.RefinementAtlas.Batch008
