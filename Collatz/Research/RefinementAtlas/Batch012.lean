import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 012. -/
namespace Collatz.Research.RefinementAtlas.Batch012
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (5, 3). -/
theorem data_5_3 : oddCount 3 5 = 2 ∧
    acceleratedOrbit 5 3 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_3 : gap 5 3 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_3 : threshold 5 3 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_3 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 3) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 3
  rw [data_5_3.1, data_5_3.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_3 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 3) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 3
  rw [data_5_3.1, data_5_3.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_3 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 3) < 32 * (2 * m) + 3 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 3 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_3] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 3) < 32 * (2 * m) + 3 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_3 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 3) < 32 * (2 * m + 1) + 3 := by
  apply refinement_cleared (k := 5) (r := 3) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_3]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 4). -/
theorem data_5_4 : oddCount 4 5 = 2 ∧
    acceleratedOrbit 5 4 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_4 : gap 5 4 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_4 : threshold 5 4 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_4 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 4) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 4
  rw [data_5_4.1, data_5_4.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_4 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 4) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 4
  rw [data_5_4.1, data_5_4.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_4 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 4) < 32 * (2 * m) + 4 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 4 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_4] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 4) < 32 * (2 * m) + 4 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_4 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 4) < 32 * (2 * m + 1) + 4 := by
  apply refinement_cleared (k := 5) (r := 4) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_4]; decide

/-- Kernel-evaluated parity count and endpoint for (5, 5). -/
theorem data_5_5 : oddCount 5 5 = 2 ∧
    acceleratedOrbit 5 5 = 2 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_5_5 : gap 5 5 = 23 ∧ 9 < 32 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_5_5 : threshold 5 5 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_5_5 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 5) = 9 * (2 * m) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m) 5
  rw [data_5_5.1, data_5_5.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_5_5 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 5) = 9 * (2 * m + 1) + 2 := by
  have h := Congruence.accOrbit_pow_two_mul_add 5 (2 * m + 1) 5
  rw [data_5_5.1, data_5_5.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_5_5 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m) + 5) < 32 * (2 * m) + 5 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 5 5 < 2 ^ 5 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_5_5] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 5 (32 * (2 * m) + 5) < 32 * (2 * m) + 5 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_5_5 (m : Nat) :
    acceleratedOrbit 5 (32 * (2 * m + 1) + 5) < 32 * (2 * m + 1) + 5 := by
  apply refinement_cleared (k := 5) (r := 5) (s := 2) (q := 1)
  · decide
  · rw [cutoff_5_5]; decide

end Collatz.Research.RefinementAtlas.Batch012
