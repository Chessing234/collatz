import Collatz.Research.RefinementAtlas.Core

/-! Sharp refined-cylinder certificates, batch 020. -/
namespace Collatz.Research.RefinementAtlas.Batch020
open Collatz
open Collatz.Research.DescentAtlas
open Collatz.Research.RefinementAtlas

/-- Kernel-evaluated parity count and endpoint for (6, 4). -/
theorem data_6_4 : oddCount 4 6 = 2 ∧
    acceleratedOrbit 6 4 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_4 : gap 6 4 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_4 : threshold 6 4 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_4 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 4) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 4
  rw [data_6_4.1, data_6_4.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_4 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 4) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 4
  rw [data_6_4.1, data_6_4.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_4 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 4) < 64 * (2 * m) + 4 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 4 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_4] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 4) < 64 * (2 * m) + 4 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_4 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 4) < 64 * (2 * m + 1) + 4 := by
  apply refinement_cleared (k := 6) (r := 4) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_4]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 5). -/
theorem data_6_5 : oddCount 5 6 = 2 ∧
    acceleratedOrbit 6 5 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_5 : gap 6 5 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_5 : threshold 6 5 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_5 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 5) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 5
  rw [data_6_5.1, data_6_5.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_5 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 5) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 5
  rw [data_6_5.1, data_6_5.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_5 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 5) < 64 * (2 * m) + 5 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 5 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_5] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 5) < 64 * (2 * m) + 5 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_5 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 5) < 64 * (2 * m + 1) + 5 := by
  apply refinement_cleared (k := 6) (r := 5) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_5]; decide

/-- Kernel-evaluated parity count and endpoint for (6, 6). -/
theorem data_6_6 : oddCount 6 6 = 2 ∧
    acceleratedOrbit 6 6 = 1 := by
  decide

/-- The coefficient deficit is strictly positive. -/
theorem gap_6_6 : gap 6 6 = 55 ∧ 9 < 64 := by
  decide

/-- The original residue cylinder has exactly this least successful index. -/
theorem cutoff_6_6 : threshold 6 6 = 0 := by
  decide

/-- Exact endpoint in the zero refinement digit, for every natural index. -/
theorem even_endpoint_6_6 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 6) = 9 * (2 * m) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m) 6
  rw [data_6_6.1, data_6_6.2] at h
  exact h

/-- Exact endpoint in the nonzero refinement digit. -/
theorem odd_endpoint_6_6 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 6) = 9 * (2 * m + 1) + 1 := by
  have h := Congruence.accOrbit_pow_two_mul_add 6 (2 * m + 1) 6
  rw [data_6_6.1, data_6_6.2] at h
  exact h

/-- The zero refinement digit retains the sharp original cutoff. -/
theorem even_cutoff_6_6 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m) + 6) < 64 * (2 * m) + 6 ↔ 0 ≤ m := by
  have hc : 3 ^ oddCount 6 6 < 2 ^ 6 := by decide
  have h := refined_descent_iff (s := 2) (q := 0) (m := m) hc
  rw [cutoff_6_6] at h
  simp only [Nat.add_zero] at h
  change acceleratedOrbit 6 (64 * (2 * m) + 6) < 64 * (2 * m) + 6 ↔ 0 ≤ 2 * m at h
  rw [h]
  omega

/-- The nonzero refinement digit has no exceptional indices. -/
theorem odd_cleared_6_6 (m : Nat) :
    acceleratedOrbit 6 (64 * (2 * m + 1) + 6) < 64 * (2 * m + 1) + 6 := by
  apply refinement_cleared (k := 6) (r := 6) (s := 2) (q := 1)
  · decide
  · rw [cutoff_6_6]; decide

end Collatz.Research.RefinementAtlas.Batch020
